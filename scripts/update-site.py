#!/usr/bin/env python3
"""Refresh the static site from the source CV and current publication data.

The updater keeps the hand-designed HTML/CSS intact and only rewrites the
content blocks when the underlying record data actually changes.

It performs four main jobs:
1. Parse the repo-copied CV (.docx) into structured publication records.
2. Merge those records with the current site so existing ADS links, summaries,
   and figure assets are preserved when possible.
3. Optionally enrich missing summaries from ADS abstracts and, if an OpenAI API
   key is available, generate concise factual summaries from the retrieved text.
4. Update the home, publications, and figures pages only when their record data
   changes, while always maintaining a persistent refresh log and state file.
"""

from __future__ import annotations

import argparse
import base64
import dataclasses
import datetime as dt
import hashlib
import html
import io
import json
import os
import re
import sys
import textwrap
import zipfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable
from urllib.parse import quote, urljoin, urlparse

import requests
from bs4 import BeautifulSoup

try:
    import fitz  # type: ignore
except Exception:  # pragma: no cover - optional dependency
    fitz = None


ROOT = Path(__file__).resolve().parents[1]
CV_SOURCE = ROOT / "automation" / "source" / "CV_ASHT.docx"
INDEX_HTML = ROOT / "index.html"
PUBLICATIONS_HTML = ROOT / "publications.html"
FIGURES_HTML = ROOT / "figures.html"
SITE_STATE = ROOT / "data" / "site-state.json"
PUBLICATION_OVERRIDES = ROOT / "data" / "publication-overrides.json"
UPDATE_LOG = ROOT / "data" / "update-log.jsonl"
LAST_REFRESH = ROOT / "data" / "last-refresh.txt"
SITEMAP = ROOT / "sitemap.xml"
FIGURES_DIR = ROOT / "images" / "figures"

SITE_BASE_URL = "https://andyto1234.github.io/"
PERSON_NAME = "Andy Shu Ho To"
PERSON_NAME_VARIANTS = (
    "To, Andy S. H.",
    "To, Andy. S. H.",
    "To, Andy S.H.",
    "To, Andy SH",
)

OPENAI_CHAT_URL = "https://api.openai.com/v1/chat/completions"

HEADERS = {
    "User-Agent": "Mozilla/5.0 (Codex site refresh; +https://andyto1234.github.io/)"
}

CURRENT_YEAR = dt.datetime.now(dt.timezone.utc).year


@dataclass
class PaperRecord:
    kind: str
    title: str
    year: int
    citation: str
    status: str
    authors_raw: str = ""
    authors_html: str = ""
    meta: str = ""
    ads_url: str | None = None
    doi_url: str | None = None
    summary: str = ""
    summary_source: str = "pending"
    figure_src: str | None = None
    figure_alt: str = ""
    figure_width: int | None = None
    figure_height: int | None = None
    figure_note: str = ""
    science_note: str = ""
    page_id: str = ""
    original_index: int = 0

    def normalized(self) -> dict[str, Any]:
        """Return the stable subset used for comparisons and state storage."""

        data = dataclasses.asdict(self)
        data.pop("authors_html", None)
        data.pop("summary", None)
        data.pop("figure_alt", None)
        data.pop("figure_note", None)
        data.pop("science_note", None)
        data.pop("original_index", None)
        return data


def normalize_whitespace(text: str) -> str:
    return re.sub(r"\s+", " ", text or "").strip()


def normalize_title(title: str) -> str:
    text = normalize_whitespace(title)
    text = text.strip('“”"\'')
    text = text.rstrip(".")
    text = text.replace("–", "-").replace("—", "-")
    return re.sub(r"\s+", " ", text).lower()


def slugify(text: str) -> str:
    text = normalize_title(text)
    text = re.sub(r"[^a-z0-9]+", "-", text)
    text = re.sub(r"-+", "-", text).strip("-")
    return text or "paper"


def escape_html(text: str) -> str:
    return html.escape(text, quote=True)


def read_docx_paragraphs(docx_path: Path) -> list[str]:
    """Extract all non-empty paragraph texts from a .docx file."""

    ns = {"w": "http://schemas.openxmlformats.org/wordprocessingml/2006/main"}
    with zipfile.ZipFile(docx_path) as archive:
        xml = archive.read("word/document.xml")

    from xml.etree import ElementTree as ET

    root = ET.fromstring(xml)
    paragraphs: list[str] = []
    for paragraph in root.findall(".//w:p", ns):
        parts = [node.text or "" for node in paragraph.findall(".//w:t", ns)]
        text = normalize_whitespace("".join(parts))
        if text:
            paragraphs.append(text)
    return paragraphs


def find_paragraph_index(paragraphs: list[str], needle: str | Iterable[str]) -> int:
    needles = {needle} if isinstance(needle, str) else set(needle)
    for index, paragraph in enumerate(paragraphs):
        if paragraph in needles:
            return index
    for index, paragraph in enumerate(paragraphs):
        if any(needle.lower() in paragraph.lower() for needle in needles):
            return index
    raise ValueError(f"Could not locate paragraph marker: {needle}")


def clean_title_text(text: str) -> str:
    return normalize_whitespace(text).strip("“”\"'")


def extract_year_from_citation(citation: str) -> int:
    match = re.search(r"\((\d{4})\)", citation)
    if match:
        return int(match.group(1))
    return CURRENT_YEAR


def extract_year_from_text(text: str) -> int:
    matches = re.findall(r"(?:19|20)\d{2}", text or "")
    if matches:
        return int(matches[-1])
    return 0


def citation_status(citation: str) -> str:
    lowered = citation.lower()
    if "accepted for publication" in lowered:
        return "accepted"
    if "submitted to" in lowered or "submitted for review" in lowered or lowered.startswith("submitted"):
        return "submitted"
    if "data set" in lowered or "dataset" in lowered:
        return "dataset"
    return "published"


def citation_venue_text(citation: str, year: int, status: str) -> str:
    """Return a short venue/status line for display."""

    if status == "dataset":
        return normalize_whitespace(citation)

    if status == "accepted":
        match = re.search(r"accepted for publication in\s+(.+?)(?:\)|$)", citation, re.I)
        if match:
            venue = normalize_whitespace(match.group(1))
            return f"{venue} · accepted for publication ({year})"
        return f"Accepted for publication ({year})"

    if status == "submitted":
        if "submitted for review" in citation.lower():
            return f"Submitted for review ({year})"
        match = re.search(r"submitted to\s+(.+?)(?:\)|$)", citation, re.I)
        if match:
            venue = normalize_whitespace(match.group(1))
            return f"Submitted to {venue} ({year})"
        return f"Submitted ({year})"

    after_year = citation
    if ")." in citation:
        after_year = citation.split(").", 1)[1]
    after_year = re.sub(r"\s*doi:.*$", "", after_year, flags=re.I).strip(" .")
    if after_year:
        return f"{after_year} ({year})"
    return str(year)


def citation_url(citation: str) -> str | None:
    """Derive a canonical link from a citation line when the current site
    does not already provide one."""

    doi_match = re.search(r"doi:([^\s)]+)", citation, re.I)
    if not doi_match:
        return None

    doi_or_code = doi_match.group(1).strip()
    if re.match(r"^\d{4}arXiv\d+[A-Z]?$", doi_or_code):
        bibcode = quote(doi_or_code, safe=".")
        return f"https://ui.adsabs.harvard.edu/abs/{bibcode}/abstract"

    if re.match(r"^\d{4}[A-Za-z].*", doi_or_code) and ("A&A" in doi_or_code or "&" in doi_or_code):
        bibcode = quote(doi_or_code, safe=".")
        return f"https://ui.adsabs.harvard.edu/abs/{bibcode}/abstract"

    if doi_or_code.lower().startswith("10."):
        return f"https://doi.org/{doi_or_code}"

    return None


def citation_authors_text(citation: str) -> str:
    """Return the author portion of a CV citation line."""

    authors = citation.split("(", 1)[0]
    return normalize_whitespace(authors).strip()


def highlight_andy(text: str) -> str:
    """Wrap the author's name in the site highlight span."""

    pattern = re.compile(
        r"To,\s*Andy(?:\.|\s)*S\.?\s*H\.?", re.IGNORECASE
    )

    def _replace(match: re.Match[str]) -> str:
        return '<span class="author-highlight">To, Andy S. H.</span>'

    return pattern.sub(_replace, text)


def short_display_authors(authors_text: str) -> str:
    """Keep the current author text but ensure Andy is highlighted."""

    text = normalize_whitespace(authors_text)
    text = text.replace("To, Andy. S. H.", "To, Andy S. H.")
    text = text.replace("To, Andy. S. H", "To, Andy S. H.")
    return highlight_andy(html.escape(text))


def read_text_file(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def write_text_file(path: Path, content: str) -> bool:
    path.parent.mkdir(parents=True, exist_ok=True)
    existing = path.read_text(encoding="utf-8") if path.exists() else None
    if existing == content:
        return False
    path.write_text(content, encoding="utf-8")
    return True


def write_json_file(path: Path, data: Any) -> bool:
    return write_text_file(path, json.dumps(data, indent=2, ensure_ascii=False) + "\n")


def parse_cv_records(paragraphs: list[str]) -> list[PaperRecord]:
    """Parse the publication and dataset sections from the CV."""

    dataset_idx = find_paragraph_index(paragraphs, "PUBLICLY AVAILABLE DATASET")
    bibliography_idx = find_paragraph_index(paragraphs, {"Bibliograhy", "Bibliography"})
    first_idx = find_paragraph_index(paragraphs, "First author publications")
    co_idx = find_paragraph_index(paragraphs, "Co-author publications")

    records: list[PaperRecord] = []

    def parse_title_pairs(start: int, end: int, kind: str) -> None:
        index = start
        while index < end:
            paragraph = normalize_whitespace(paragraphs[index])
            if not paragraph or not paragraph.startswith(("“", '"')):
                index += 1
                continue

            if index + 1 >= end:
                break

            title = clean_title_text(paragraph)
            citation = normalize_whitespace(paragraphs[index + 1])
            year = extract_year_from_citation(citation)
            status = citation_status(citation)
            record = PaperRecord(
                kind=kind,
                title=title,
                year=year,
                citation=citation,
                status=status,
                authors_raw=citation_authors_text(citation),
                meta=citation_venue_text(citation, year, status),
                ads_url=citation_url(citation),
                page_id=f"{kind}-{year}-{slugify(title)}",
                original_index=len(records),
            )
            records.append(record)
            index += 2

    parse_title_pairs(first_idx + 1, co_idx, "first-author")
    parse_title_pairs(co_idx + 1, len(paragraphs), "collaborative")

    # The dataset entry in the CV is written as a year-prefixed quoted title.
    dataset_title = ""
    dataset_citation = ""
    if dataset_idx + 1 < bibliography_idx:
        dataset_title = normalize_whitespace(paragraphs[dataset_idx + 1])
    if dataset_idx + 2 < bibliography_idx:
        dataset_citation = normalize_whitespace(paragraphs[dataset_idx + 2])
    if dataset_title:
        dataset_title = re.sub(r"^\d{4}\s*", "", dataset_title)
        dataset_title = clean_title_text(dataset_title)
        year = extract_year_from_citation(dataset_citation)
        status = "dataset"
        records.append(
            PaperRecord(
                kind="dataset",
                title=dataset_title,
                year=year,
                citation=dataset_citation,
                status=status,
                authors_raw=citation_authors_text(dataset_citation),
                meta=citation_venue_text(dataset_citation, year, status),
                page_id=f"dataset-{year}-{slugify(dataset_title)}",
                original_index=len(records),
            )
        )
    return records


def parse_current_publications(html_text: str) -> dict[str, dict[str, Any]]:
    soup = BeautifulSoup(html_text, "lxml")
    data: dict[str, dict[str, Any]] = {}
    for item in soup.select("ol[data-publication-list] > li.publication-list__item"):
        card = item.select_one(".publication-card")
        if not card:
            continue
        title_node = card.select_one(".publication-list__title")
        if not title_node:
            continue
        title_link = title_node.find("a")
        title = normalize_whitespace(title_link.get_text(" ", strip=True) if title_link else title_node.get_text(" ", strip=True))
        key = normalize_title(title)
        authors_node = card.select_one(".publication-card__authors")
        meta_node = card.select_one(".publication-card__meta")
        abstract_node = card.select_one(".publication-card__abstract p:not(.publication-card__abstract-label)")
        chip_node = card.select_one(".bibliography-entry__chip")
        link_node = card.select_one(".bibliography-entry__link, .publication-list__title a")
        data[key] = {
            "title": title,
            "kind": item.get("data-kind", ""),
            "year": int(item.get("data-year", "0") or 0),
            "authors_html": authors_node.decode_contents().strip() if authors_node else "",
            "authors_text": normalize_whitespace(authors_node.get_text(" ", strip=True)) if authors_node else "",
            "meta": normalize_whitespace(meta_node.get_text(" ", strip=True)) if meta_node else "",
            "summary": normalize_whitespace(abstract_node.get_text(" ", strip=True)) if abstract_node else "",
            "chip": normalize_whitespace(chip_node.get_text(" ", strip=True)) if chip_node else "",
            "url": link_node.get("href") if link_node and link_node.has_attr("href") else None,
        }
    return data


def parse_current_selected(html_text: str) -> dict[str, dict[str, Any]]:
    soup = BeautifulSoup(html_text, "lxml")
    data: dict[str, dict[str, Any]] = {}
    for item in soup.select("#selected-publications .publication-list__item"):
        card = item.select_one(".publication-card")
        if not card:
            continue
        title_node = card.select_one(".publication-list__title")
        if not title_node:
            continue
        title_link = title_node.find("a")
        title = normalize_whitespace(title_link.get_text(" ", strip=True) if title_link else title_node.get_text(" ", strip=True))
        key = normalize_title(title)
        authors_node = card.select_one(".publication-card__authors")
        meta_node = card.select_one(".publication-card__meta")
        abstract_node = card.select_one(".publication-card__abstract p:not(.publication-card__abstract-label)")
        data[key] = {
            "title": title,
            "authors_html": authors_node.decode_contents().strip() if authors_node else "",
            "authors_text": normalize_whitespace(authors_node.get_text(" ", strip=True)) if authors_node else "",
            "meta": normalize_whitespace(meta_node.get_text(" ", strip=True)) if meta_node else "",
            "summary": normalize_whitespace(abstract_node.get_text(" ", strip=True)) if abstract_node else "",
            "url": title_link.get("href") if title_link and title_link.has_attr("href") else None,
        }
    return data


def parse_current_figures(html_text: str) -> dict[str, dict[str, Any]]:
    soup = BeautifulSoup(html_text, "lxml")
    data: dict[str, dict[str, Any]] = {}
    for section in soup.select(".figure-showcase"):
        heading = section.select_one("h2")
        image = section.select_one("figure.figure-showcase__media img")
        meta = section.select_one(".figure-showcase__meta")
        science = section.select(".figure-showcase__text-block p:not(.figure-showcase__label)")
        links = section.select(".figure-showcase__links a")
        if not heading or not image:
            continue
        title = normalize_whitespace(heading.get_text(" ", strip=True))
        key = normalize_title(title)
        meta_text = normalize_whitespace(meta.get_text(" ", strip=True)) if meta else ""
        data[key] = {
            "title": title,
            "year": extract_year_from_text(meta_text),
            "image_src": image.get("src"),
            "image_alt": image.get("alt", ""),
            "image_width": int(image.get("width", "0") or 0),
            "image_height": int(image.get("height", "0") or 0),
            "meta": meta_text,
            "science_note": normalize_whitespace(science[0].get_text(" ", strip=True)) if len(science) > 0 else "",
            "figure_note": normalize_whitespace(science[1].get_text(" ", strip=True)) if len(science) > 1 else "",
            "ads_url": links[0].get("href") if links else None,
            "page_id": section.get("id", ""),
        }
    return data


def load_previous_state() -> dict[str, Any]:
    if not SITE_STATE.exists():
        return {}
    try:
        return json.loads(read_text_file(SITE_STATE))
    except Exception:
        return {}


def load_publication_overrides() -> dict[str, dict[str, Any]]:
    """Load curated publication metadata keyed by the title used in the CV.

    The source CV is intentionally not rewritten by the automated site refresh.
    Overrides let a newly published paper replace its accepted/submitted metadata
    with the canonical journal title, citation, and DOI on every future run.
    """

    if not PUBLICATION_OVERRIDES.exists():
        return {}
    try:
        raw = json.loads(read_text_file(PUBLICATION_OVERRIDES))
    except Exception as exc:
        raise ValueError(f"Could not read publication overrides: {exc}") from exc
    if not isinstance(raw, dict):
        raise ValueError("Publication overrides must be a JSON object keyed by title.")
    return {
        normalize_title(title): values
        for title, values in raw.items()
        if isinstance(title, str) and isinstance(values, dict)
    }


def merge_records(
    cv_records: list[PaperRecord],
    current_publications: dict[str, dict[str, Any]],
    current_selected: dict[str, dict[str, Any]],
    current_figures: dict[str, dict[str, Any]],
    previous_state: dict[str, Any],
    *,
    offline: bool,
    openai_api_key: str | None,
    openai_model: str,
) -> list[PaperRecord]:
    prev_index = {
        normalize_title(entry.get("title", "")): entry
        for entry in previous_state.get("records", [])
    }
    merged: list[PaperRecord] = []
    overrides = load_publication_overrides()

    for record in cv_records:
        key = normalize_title(record.title)
        override = overrides.get(key) or {}
        canonical_key = normalize_title(str(override.get("title") or record.title))
        pub = (
            current_publications.get(canonical_key)
            or current_selected.get(canonical_key)
            or current_publications.get(key)
            or current_selected.get(key)
            or {}
        )
        fig = current_figures.get(canonical_key) or current_figures.get(key) or {}
        prev = prev_index.get(canonical_key) or prev_index.get(key) or {}

        record.ads_url = pub.get("url") or fig.get("ads_url") or citation_url(record.citation)
        record.doi_url = pub.get("doi_url")
        authors_text = pub.get("authors_text") or citation_authors_text(record.citation)
        record.authors_html = pub.get("authors_html") or highlight_andy(html.escape(authors_text))
        record.authors_raw = authors_text
        record.meta = pub.get("meta") or fig.get("meta") or citation_venue_text(record.citation, record.year, record.status)
        record.summary = pub.get("summary") or prev.get("summary") or ""
        record.summary_source = pub.get("summary_source") or prev.get("summary_source") or "pending"
        record.figure_src = fig.get("image_src") or prev.get("figure_src")
        record.figure_alt = fig.get("image_alt") or prev.get("figure_alt") or ""
        record.figure_width = fig.get("image_width") or prev.get("figure_width")
        record.figure_height = fig.get("image_height") or prev.get("figure_height")
        record.figure_note = fig.get("figure_note") or prev.get("figure_note") or ""
        record.science_note = fig.get("science_note") or prev.get("science_note") or ""
        record.page_id = fig.get("page_id") or prev.get("page_id") or record.page_id

        for field_name in ("title", "year", "citation", "status", "meta", "ads_url", "doi_url"):
            if field_name in override:
                setattr(record, field_name, override[field_name])

        if not record.summary or record.summary_source == "pending":
            abstract = fetch_abstract_text(record.ads_url, offline=offline)
            if abstract:
                record.summary = summarize_text(
                    title=record.title,
                    source_text=abstract,
                    api_key=openai_api_key,
                    model=openai_model,
                )
                record.summary_source = "abstract" if "Summary to be provided later" not in record.summary else "pending"
            elif record.summary:
                record.summary_source = "site"
            else:
                record.summary = "Summary to be provided later."
                record.summary_source = "pending"
        else:
            # Keep current or previously generated summary verbatim.
            record.summary = record.summary.strip()
            if record.summary_source not in {"site", "abstract", "paper"}:
                record.summary_source = "site"

        if record.kind == "first-author":
            if not record.figure_src:
                pdf_url = discover_pdf_url(record.ads_url, offline=offline)
                if pdf_url:
                    figure_result = select_representative_figure(
                        title=record.title,
                        pdf_url=pdf_url,
                        output_slug=slugify(record.title),
                        api_key=openai_api_key,
                        model=openai_model,
                        offline=offline,
                    )
                    if figure_result:
                        record.figure_src = figure_result["image_src"]
                        record.figure_alt = figure_result["image_alt"]
                        record.figure_width = figure_result["image_width"]
                        record.figure_height = figure_result["image_height"]
                        record.figure_note = figure_result["figure_note"]
                        record.science_note = figure_result["science_note"]
                        record.page_id = figure_result["page_id"]

        merged.append(record)

    merged.sort(key=lambda item: (-item.year, 0 if item.kind == "first-author" else 1, item.original_index))
    return merged


def fetch_url(url: str, *, offline: bool = False, timeout: int = 30) -> str | None:
    if not url or offline:
        return None
    try:
        response = requests.get(url, headers=HEADERS, timeout=timeout)
        response.raise_for_status()
        return response.text
    except Exception:
        return None


def fetch_binary(url: str, *, offline: bool = False, timeout: int = 30) -> bytes | None:
    if not url or offline:
        return None
    try:
        response = requests.get(url, headers=HEADERS, timeout=timeout)
        response.raise_for_status()
        return response.content
    except Exception:
        return None


def arxiv_id_from_url(url: str | None) -> str | None:
    if not url:
        return None

    match = re.search(r"arxiv\.org/(?:abs|pdf)/(\d{4}\.\d+)", url, re.I)
    if match:
        return match.group(1)

    match = re.search(r"/abs/\d{4}arXiv(\d{4})(\d+)[A-Z]?/abstract", url, re.I)
    if match:
        return f"{match.group(1)}.{match.group(2)}"

    return None


def fetch_abstract_text(url: str | None, *, offline: bool = False) -> str | None:
    if not url or offline:
        return None

    arxiv_id = arxiv_id_from_url(url)
    if arxiv_id:
        arxiv_html = fetch_url(f"https://arxiv.org/abs/{arxiv_id}", offline=offline)
        if arxiv_html:
            soup = BeautifulSoup(arxiv_html, "lxml")
            abstract = soup.select_one("blockquote.abstract")
            if abstract:
                text = normalize_whitespace(abstract.get_text(" ", strip=True))
                text = re.sub(r"^(abstract|summary)\s*[:\-]?\s*", "", text, flags=re.I)
                if len(text) > 160:
                    return text

    html_text = fetch_url(url, offline=offline)
    if not html_text:
        return None
    soup = BeautifulSoup(html_text, "lxml")

    # Common metadata on ADS / DOI landing pages.
    meta_description = soup.find("meta", attrs={"name": "description"})
    if meta_description and meta_description.get("content"):
        content = normalize_whitespace(meta_description["content"])
        if len(content) > 160 and "adsabs" not in content.lower():
            return content

    for selector in [
        "blockquote.abstract",
        ".abstract",
        "[data-abstract]",
        ".article__abstract",
        ".article-section__abstract",
        ".description",
    ]:
        node = soup.select_one(selector)
        if node:
            text = normalize_whitespace(node.get_text(" ", strip=True))
            text = re.sub(r"^(abstract|summary)\s*[:\-]?\s*", "", text, flags=re.I)
            if len(text) > 160:
                return text

    text = normalize_whitespace(soup.get_text(" ", strip=True))
    if len(text) > 500:
        # Try to isolate a paragraph that looks like an abstract.
        sentences = re.split(r"(?<=[.!?])\s+", text)
        abstract = " ".join(sentences[:6]).strip()
        if len(abstract) > 160:
            return abstract
    return None


def discover_pdf_url(url: str | None, *, offline: bool = False) -> str | None:
    if not url or offline:
        return None
    arxiv_id = arxiv_id_from_url(url)
    if arxiv_id:
        return f"https://arxiv.org/pdf/{arxiv_id}"

    html_text = fetch_url(url, offline=offline)
    if not html_text:
        return None
    soup = BeautifulSoup(html_text, "lxml")

    candidates: list[str] = []
    for link in soup.find_all("a", href=True):
        href = link["href"]
        text = normalize_whitespace(link.get_text(" ", strip=True)).lower()
        href_lower = href.lower()
        if any(token in href_lower for token in ("pdf", "download", "article-pdf", "fulltext")):
            candidates.append(urljoin(url, href))
        elif "pdf" in text or "download" in text:
            candidates.append(urljoin(url, href))

    for candidate in candidates:
        if candidate.lower().endswith(".pdf") or "pdf" in candidate.lower():
            return candidate

    return None


def extract_pdf_pages(pdf_bytes: bytes, max_pages: int = 6) -> list[dict[str, Any]]:
    if fitz is None:
        return []

    document = fitz.open(stream=pdf_bytes, filetype="pdf")
    pages: list[dict[str, Any]] = []
    for page_index in range(min(len(document), max_pages)):
        page = document[page_index]
        text = normalize_whitespace(page.get_text("text"))
        page_dict = page.get_text("dict")
        image_area = 0.0
        text_area = 0.0
        for block in page_dict.get("blocks", []):
            bbox = block.get("bbox")
            if not bbox:
                continue
            area = abs((bbox[2] - bbox[0]) * (bbox[3] - bbox[1]))
            if block.get("type") == 1:
                image_area += area
            elif block.get("type") == 0:
                text_area += area
        pages.append(
            {
                "page_index": page_index,
                "text": text,
                "image_area": image_area,
                "text_area": text_area,
                "score": image_area - text_area * 0.12,
            }
        )
    return pages


def render_pdf_page(pdf_bytes: bytes, page_index: int, output_path: Path, scale: float = 2.0) -> None:
    if fitz is None:
        raise RuntimeError("PyMuPDF is not installed")

    document = fitz.open(stream=pdf_bytes, filetype="pdf")
    page = document[page_index]
    matrix = fitz.Matrix(scale, scale)
    pix = page.get_pixmap(matrix=matrix, alpha=False)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    pix.save(str(output_path))


def summarize_text(
    *,
    title: str,
    source_text: str | None,
    api_key: str | None,
    model: str,
) -> str:
    source_text = normalize_whitespace(source_text or "")
    if not source_text:
        return "Summary to be provided later."

    if not api_key:
        return sentence_summary(source_text)

    prompt = textwrap.dedent(
        f"""
        Write a concise, factual 2-sentence summary for the following paper.
        Use only the source text, keep the wording neutral, and do not add hype.
        If the source text is too sparse to support a summary, return exactly:
        Summary to be provided later.

        Title: {title}

        Source text:
        {source_text}
        """
    ).strip()

    try:
        response = requests.post(
            OPENAI_CHAT_URL,
            headers={
                "Authorization": f"Bearer {api_key}",
                "Content-Type": "application/json",
            },
            json={
                "model": model,
                "messages": [
                    {
                        "role": "system",
                        "content": "You write concise academic summaries that are strictly factual.",
                    },
                    {"role": "user", "content": prompt},
                ],
                "temperature": 0.2,
                "max_tokens": 220,
            },
            timeout=60,
        )
        response.raise_for_status()
        payload = response.json()
        content = payload["choices"][0]["message"]["content"].strip()
        return normalize_whitespace(content)
    except Exception:
        return sentence_summary(source_text)


def sentence_summary(text: str) -> str:
    sentences = re.split(r"(?<=[.!?])\s+", normalize_whitespace(text))
    summary = " ".join(sentences[:2]).strip()
    if len(summary) < 80:
        return "Summary to be provided later."
    return summary


def select_representative_figure(
    *,
    title: str,
    pdf_url: str,
    output_slug: str,
    api_key: str | None,
    model: str,
    offline: bool,
) -> dict[str, Any] | None:
    pdf_bytes = fetch_binary(pdf_url, offline=offline)
    if not pdf_bytes:
        return None

    output_path = FIGURES_DIR / f"{output_slug}.png"
    page_choice = 0
    page_meta = extract_pdf_pages(pdf_bytes)
    if page_meta:
        page_choice = max(page_meta, key=lambda item: item["score"])["page_index"]

    # If we can render the candidate page, prefer that. Otherwise keep the
    # existing figure asset untouched.
    try:
        render_pdf_page(pdf_bytes, page_choice, output_path)
    except Exception:
        return None

    # If an OpenAI key is available, allow a vision pass to refine the choice.
    # We only use it when multiple pages are available and render the chosen
    # page plus a small neighbourhood as thumbnails.
    if api_key and fitz is not None and len(page_meta) > 1:
        try:
            # We keep the heuristic result if the API pass fails.
            chosen = choose_pdf_page_with_openai(
                title=title,
                pdf_bytes=pdf_bytes,
                candidate_pages=page_meta[: min(4, len(page_meta))],
                api_key=api_key,
                model=model,
            )
            if chosen is not None and 0 <= chosen < len(page_meta):
                page_choice = chosen
                render_pdf_page(pdf_bytes, page_choice, output_path)
        except Exception:
            pass

    record = {
        "image_src": f"./images/figures/{output_slug}.png",
        "image_alt": f"Representative figure from {title}",
        "image_width": None,
        "image_height": None,
        "figure_note": "Representative figure selected automatically from the paper PDF.",
        "science_note": "Automatically selected representative figure for the first-author paper.",
        "page_id": f"paper-{slugify(title)}",
    }

    try:
        if fitz is not None:
            document = fitz.open(stream=pdf_bytes, filetype="pdf")
            pix = document[page_choice].get_pixmap(matrix=fitz.Matrix(2.0, 2.0), alpha=False)
            record["image_width"] = pix.width
            record["image_height"] = pix.height
    except Exception:
        pass

    return record


def choose_pdf_page_with_openai(
    *,
    title: str,
    pdf_bytes: bytes,
    candidate_pages: list[dict[str, Any]],
    api_key: str,
    model: str,
) -> int | None:
    if fitz is None:
        return None

    document = fitz.open(stream=pdf_bytes, filetype="pdf")
    content: list[dict[str, Any]] = [
        {
            "type": "text",
            "text": (
                "Choose the single most representative page for a paper figure. "
                "Prefer a clear scientific plot or schematic over text-heavy pages. "
                "Return only the zero-based page index."
            ),
        },
        {"type": "text", "text": f"Paper title: {title}"},
    ]

    thumbnails: list[tuple[int, str]] = []
    for entry in candidate_pages:
        page = document[entry["page_index"]]
        pix = page.get_pixmap(matrix=fitz.Matrix(0.6, 0.6), alpha=False)
        png_bytes = pix.tobytes("png")
        thumbnails.append((entry["page_index"], base64.b64encode(png_bytes).decode("ascii")))

    for page_index, encoded in thumbnails:
        content.append(
            {
                "type": "image_url",
                "image_url": {
                    "url": f"data:image/png;base64,{encoded}",
                    "detail": "low",
                },
            }
        )
        content.append({"type": "text", "text": f"Thumbnail for page {page_index}."})

    response = requests.post(
        OPENAI_CHAT_URL,
        headers={
            "Authorization": f"Bearer {api_key}",
            "Content-Type": "application/json",
        },
        json={
            "model": model,
            "messages": [
                {
                    "role": "system",
                    "content": "You choose a single representative scientific figure page.",
                },
                {"role": "user", "content": content},
            ],
            "temperature": 0.0,
            "max_tokens": 16,
        },
        timeout=90,
    )
    response.raise_for_status()
    text = normalize_whitespace(response.json()["choices"][0]["message"]["content"])
    match = re.search(r"(\d+)", text)
    if not match:
        return None
    return int(match.group(1))


def render_publication_card(record: PaperRecord, summary_id: str | None = None) -> str:
    title_html = escape_html(record.title)
    primary_url = record.doi_url or record.ads_url
    if primary_url:
        title_html = (
            f'<a href="{escape_html(primary_url)}" target="_blank" rel="noreferrer noopener">'
            f"{title_html}</a>"
        )

    eyebrow = f"{record.year} · {record.kind.replace('-', ' ').title()}"
    chip = ""
    if record.status in {"accepted", "submitted", "dataset"}:
        chip = f'<span class="bibliography-entry__chip">{record.status.title()}</span>'

    actions: list[str] = []
    if primary_url:
        link_label = "Published paper" if record.doi_url else "ADS abstract"
        actions.append(
            f'<a class="bibliography-entry__link" href="{escape_html(primary_url)}" target="_blank" rel="noreferrer noopener">{link_label}</a>'
        )

    abstract_html = ""
    if record.summary:
        if not summary_id:
            summary_id = f"pub-summary-{slugify(record.title)}"
        abstract_html = textwrap.dedent(
            f"""
            <div class="publication-card__abstract" id="{escape_html(summary_id)}">
              <div class="publication-card__abstract-inner">
                <p class="publication-card__abstract-label">Summary</p>
                <p>{escape_html(record.summary)}</p>
              </div>
            </div>
            """
        ).strip()
        actions.append(
            textwrap.dedent(
                f"""
                <button class="publication-card__toggle" type="button" aria-expanded="false" aria-controls="{escape_html(summary_id)}" aria-label="Show summary for {escape_html(record.title)}">
                  <span class="publication-card__toggle-label">Summary</span>
                  <svg viewBox="0 0 24 24" aria-hidden="true"><path d="M8 10l4 4 4-4"></path></svg>
                </button>
                """
            ).strip()
        )

    return textwrap.dedent(
        f"""
        <li class="publication-list__item" data-kind="{escape_html(record.kind)}" data-year="{record.year}">
          <article class="publication-card publication-card--bibliography">
            <div class="publication-card__header" data-publication-trigger>
              <div class="publication-card__copy">
                <p class="publication-card__eyebrow">{escape_html(eyebrow)}</p>
                <p class="publication-list__title">{title_html}</p>
                <p class="publication-card__authors">{record.authors_html or escape_html(record.authors_raw)}</p>
                <p class="publication-card__meta">{escape_html(record.meta)}</p>
              </div>
              <div class="publication-card__actions">
                {chip}
                {' '.join(actions)}
              </div>
            </div>
            {abstract_html}
          </article>
        </li>
        """
    ).strip()


def render_selected_publication_card(record: PaperRecord, index: int) -> str:
    summary_id = f"abstract-{record.year}-{slugify(record.title)}"
    primary_url = record.doi_url or record.ads_url
    title_html = (
        f'<a href="{escape_html(primary_url)}" target="_blank" rel="noreferrer noopener">{escape_html(record.title)}</a>'
        if primary_url
        else escape_html(record.title)
    )
    chip = ""
    if record.status in {"accepted", "submitted"}:
        chip = f'<span class="bibliography-entry__chip">{record.status.title()}</span>'
    actions = []
    if primary_url:
        link_label = "Published paper" if record.doi_url else "ADS abstract"
        actions.append(
            f'<a class="bibliography-entry__link" href="{escape_html(primary_url)}" target="_blank" rel="noreferrer noopener">{link_label}</a>'
        )
    if record.summary:
        actions.append(
            f'<button class="publication-card__toggle" type="button" aria-expanded="false" aria-controls="{summary_id}" aria-label="Show summary for {escape_html(record.title)}"><span class="publication-card__toggle-label">Summary</span><svg viewBox="0 0 24 24" aria-hidden="true"><path d="M8 10l4 4 4-4"></path></svg></button>'
        )

    abstract_html = ""
    if record.summary:
        abstract_html = textwrap.dedent(
            f"""
            <div class="publication-card__abstract" id="{summary_id}">
              <div class="publication-card__abstract-inner">
                <p class="publication-card__abstract-label">Summary</p>
                <p>{escape_html(record.summary)}</p>
              </div>
            </div>
            """
        ).strip()

    return textwrap.dedent(
        f"""
        <li class="publication-list__item">
          <article class="publication-card publication-card--bibliography">
            <div class="publication-card__header" data-publication-trigger>
              <div class="publication-card__copy">
                <p class="publication-card__eyebrow">{record.year} · First author</p>
                <p class="publication-list__title">{title_html}</p>
                <p class="publication-card__authors">{record.authors_html or escape_html(record.authors_raw)}</p>
                <p class="publication-card__meta">{escape_html(record.meta)}</p>
              </div>
              <div class="publication-card__actions">
                {chip}
                {' '.join(actions)}
              </div>
            </div>
            {abstract_html}
          </article>
        </li>
        """
    ).strip()


def render_figure_showcase(record: PaperRecord) -> str:
    if not record.figure_src:
        figure_html = textwrap.dedent(
            f"""
            <figure class="figure-showcase__media figure-showcase__media--empty">
              <div class="figure-showcase__placeholder">
                <p>Figure to be selected later.</p>
                <p>{escape_html(record.title)}</p>
              </div>
            </figure>
            """
        ).strip()
    else:
        width_attr = f' width="{record.figure_width}"' if record.figure_width else ""
        height_attr = f' height="{record.figure_height}"' if record.figure_height else ""
        figure_html = textwrap.dedent(
            f"""
            <figure class="figure-showcase__media">
              <img src="{escape_html(record.figure_src)}" alt="{escape_html(record.figure_alt or f"Representative figure from {record.title}")}"{width_attr}{height_attr} />
            </figure>
            """
        ).strip()

    science = record.science_note or record.summary
    figure_note = record.figure_note or "Representative figure selected from the paper."
    link_html = ""
    primary_url = record.doi_url or record.ads_url
    if primary_url:
        link_label = "Published paper" if record.doi_url else "ADS abstract"
        link_html = (
            f'<a href="{escape_html(primary_url)}" target="_blank" rel="noreferrer noopener">{link_label}</a>'
        )

    return textwrap.dedent(
        f"""
        <section class="content-section figure-showcase" id="{escape_html(record.page_id or f"paper-{slugify(record.title)}")}">
          <p class="section-tag"><span class="section-tag__dot" aria-hidden="true"></span><span>{record.year}</span></p>
          <div class="figure-showcase__grid">
            {figure_html}
            <div class="figure-showcase__body">
              <div>
                <h2>{escape_html(record.title)}</h2>
                <p class="figure-showcase__meta">{escape_html(record.meta)}</p>
              </div>
              <div class="figure-showcase__text-block">
                <p class="figure-showcase__label">Science</p>
                <p>{escape_html(science)}</p>
              </div>
              <div class="figure-showcase__text-block">
                <p class="figure-showcase__label">Figure</p>
                <p>{escape_html(figure_note)}</p>
              </div>
              <div class="figure-showcase__links">{link_html}</div>
            </div>
          </div>
        </section>
        """
    ).strip()


def small_number_label(value: int) -> str:
    words = {
        0: "zero",
        1: "one",
        2: "two",
        3: "three",
        4: "four",
        5: "five",
        6: "six",
        7: "seven",
        8: "eight",
        9: "nine",
        10: "ten",
    }
    return words.get(value, str(value))


def schema_article_items(records: list[PaperRecord]) -> list[dict[str, Any]]:
    first_author = [record for record in records if record.kind == "first-author"]
    return [
        {
            "@type": "ListItem",
            "position": index,
            "item": {
                "@type": "ScholarlyArticle",
                "name": record.title.rstrip("."),
                "url": record.doi_url or record.ads_url or SITE_BASE_URL,
            },
        }
        for index, record in enumerate(first_author, start=1)
    ]


def update_item_list_schema(soup: BeautifulSoup, records: list[PaperRecord]) -> None:
    items = schema_article_items(records)
    for script in soup.find_all("script", attrs={"type": "application/ld+json"}):
        raw = script.string or script.get_text()
        if not raw:
            continue
        try:
            data = json.loads(raw)
        except json.JSONDecodeError:
            continue

        changed = False
        graph = data.get("@graph", []) if isinstance(data, dict) else []
        for node in graph:
            main_entity = node.get("mainEntity") if isinstance(node, dict) else None
            if isinstance(main_entity, dict) and main_entity.get("@type") == "ItemList":
                main_entity["numberOfItems"] = len(items)
                main_entity["itemListElement"] = items
                changed = True

        if changed:
            script.string = json.dumps(data, indent=6, ensure_ascii=False)


def figure_index_label(record: PaperRecord, duplicate_years: set[int]) -> str:
    if record.year not in duplicate_years:
        return str(record.year)
    short_title = record.title.rstrip(".")
    if len(short_title) > 54:
        short_title = short_title[:51].rstrip() + "..."
    return f"{record.year} - {short_title}"


def build_publications_list(records: list[PaperRecord]) -> str:
    return "\n".join(render_publication_card(record) for record in records)


def build_selected_publications(records: list[PaperRecord]) -> str:
    first_author = [record for record in records if record.kind == "first-author"]
    return "\n".join(render_selected_publication_card(record, index) for index, record in enumerate(first_author[:5], start=1))


def build_figures_sections(records: list[PaperRecord]) -> str:
    first_author = [record for record in records if record.kind == "first-author"]
    return "\n".join(render_figure_showcase(record) for record in first_author)


def publication_state_from_record(record: PaperRecord) -> dict[str, Any]:
    return {
        "title": normalize_whitespace(record.title),
        "kind": record.kind,
        "year": record.year,
        "authors_html": normalize_whitespace(record.authors_html),
        "meta": normalize_whitespace(record.meta),
        "summary": normalize_whitespace(record.summary),
        "chip": record.status.title() if record.status in {"accepted", "submitted", "dataset"} else "",
        "url": record.doi_url or record.ads_url or "",
    }


def publication_state_from_current(entry: dict[str, Any]) -> dict[str, Any]:
    return {
        "title": normalize_whitespace(entry.get("title", "")),
        "kind": normalize_whitespace(entry.get("kind", "")),
        "year": int(entry.get("year", 0) or 0),
        "authors_html": normalize_whitespace(entry.get("authors_html", "")),
        "meta": normalize_whitespace(entry.get("meta", "")),
        "summary": normalize_whitespace(entry.get("summary", "")),
        "chip": normalize_whitespace(entry.get("chip", "")),
        "url": normalize_whitespace(entry.get("url", "")),
    }


def sorted_publication_state_from_records(records: list[PaperRecord]) -> list[dict[str, Any]]:
    items = [publication_state_from_record(record) for record in records]
    return sorted(
        items,
        key=lambda item: (-item["year"], 0 if item["kind"] == "first-author" else 1, item["title"]),
    )


def sorted_publication_state_from_current(entries: dict[str, dict[str, Any]]) -> list[dict[str, Any]]:
    items = [publication_state_from_current(entry) for entry in entries.values()]
    return sorted(
        items,
        key=lambda item: (-item["year"], 0 if item["kind"] == "first-author" else 1, item["title"]),
    )


def selected_state_from_records(records: list[PaperRecord]) -> list[dict[str, Any]]:
    selected = [record for record in records if record.kind == "first-author"][:5]
    items = [
        {
            "title": normalize_whitespace(record.title),
            "year": record.year,
            "authors_html": normalize_whitespace(record.authors_html),
            "meta": normalize_whitespace(record.meta),
            "summary": normalize_whitespace(record.summary),
            "url": record.doi_url or record.ads_url or "",
        }
        for record in selected
    ]
    return items


def selected_state_from_current(entries: dict[str, dict[str, Any]]) -> list[dict[str, Any]]:
    items = [
        {
            "title": normalize_whitespace(entry.get("title", "")),
            "year": int(entry.get("year", 0) or extract_year_from_text(entry.get("meta", "")) or 0),
            "authors_html": normalize_whitespace(entry.get("authors_html", "")),
            "meta": normalize_whitespace(entry.get("meta", "")),
            "summary": normalize_whitespace(entry.get("summary", "")),
            "url": normalize_whitespace(entry.get("url", "")),
        }
        for entry in entries.values()
    ]
    return items


def figure_state_from_record(record: PaperRecord) -> dict[str, Any]:
    return {
        "title": normalize_whitespace(record.title),
        "year": record.year,
        "page_id": record.page_id,
        "image_src": normalize_whitespace(record.figure_src or ""),
        "image_alt": normalize_whitespace(record.figure_alt or ""),
        "image_width": record.figure_width or 0,
        "image_height": record.figure_height or 0,
        "meta": normalize_whitespace(record.meta),
        "science_note": normalize_whitespace(record.science_note),
        "figure_note": normalize_whitespace(record.figure_note),
        "ads_url": record.doi_url or record.ads_url or "",
    }


def figure_state_from_current(entry: dict[str, Any]) -> dict[str, Any]:
    return {
        "title": normalize_whitespace(entry.get("title", "")),
        "year": int(entry.get("year", 0) or 0),
        "page_id": normalize_whitespace(entry.get("page_id", "")),
        "image_src": normalize_whitespace(entry.get("image_src", "")),
        "image_alt": normalize_whitespace(entry.get("image_alt", "")),
        "image_width": int(entry.get("image_width", 0) or 0),
        "image_height": int(entry.get("image_height", 0) or 0),
        "meta": normalize_whitespace(entry.get("meta", "")),
        "science_note": normalize_whitespace(entry.get("science_note", "")),
        "figure_note": normalize_whitespace(entry.get("figure_note", "")),
        "ads_url": normalize_whitespace(entry.get("ads_url", "")),
    }


def sorted_figure_state_from_records(records: list[PaperRecord]) -> list[dict[str, Any]]:
    items = [figure_state_from_record(record) for record in records if record.kind == "first-author"]
    return sorted(items, key=lambda item: (-item["year"], item["title"]))


def sorted_figure_state_from_current(entries: dict[str, dict[str, Any]]) -> list[dict[str, Any]]:
    items = [figure_state_from_current(entry) for entry in entries.values()]
    return sorted(items, key=lambda item: (-item["year"], item["title"]))


def state_equals(left: list[dict[str, Any]], right: list[dict[str, Any]]) -> bool:
    return json.dumps(left, sort_keys=True, ensure_ascii=False) == json.dumps(
        right, sort_keys=True, ensure_ascii=False
    )


def get_record_signature(records: list[PaperRecord], *, include_summary: bool = True) -> str:
    payload = []
    for record in records:
        item = record.normalized()
        if include_summary:
            item["summary"] = normalize_whitespace(record.summary)
        payload.append(item)
    return hashlib.sha256(
        json.dumps(payload, sort_keys=True, ensure_ascii=False).encode("utf-8")
    ).hexdigest()


def update_publications_page(records: list[PaperRecord]) -> bool:
    html_text = read_text_file(PUBLICATIONS_HTML)
    soup = BeautifulSoup(html_text, "lxml")
    update_item_list_schema(soup, records)

    counts = {
        "all": len(records),
        "first-author": sum(1 for record in records if record.kind == "first-author"),
        "collaborative": sum(1 for record in records if record.kind == "collaborative"),
        "dataset": sum(1 for record in records if record.kind == "dataset"),
    }

    for button in soup.select(".publication-filter[data-publication-order]"):
        mode = button.get("data-publication-order", "")
        count_node = button.select_one(".publication-filter__count")
        if not count_node:
            continue
        count = counts.get(mode, 0)
        count_node.string = str(count)
        count_node["aria-label"] = f"{count} {mode.replace('-', ' ')} records"

    list_node = soup.select_one("[data-publication-list]")
    if list_node is None:
        raise RuntimeError("Could not locate publication list container.")

    list_node.clear()
    fragment = BeautifulSoup(build_publications_list(records), "lxml")
    for child in fragment.body.contents if fragment.body else fragment.contents:
        if getattr(child, "name", None):
            list_node.append(child)

    changed = write_text_file(PUBLICATIONS_HTML, serialize_document(soup))
    return changed


def update_home_page(records: list[PaperRecord]) -> bool:
    html_text = read_text_file(INDEX_HTML)
    soup = BeautifulSoup(html_text, "lxml")

    list_node = soup.select_one("#selected-publications ol.publication-list--numbered")
    if list_node is None:
        raise RuntimeError("Could not locate selected publications list.")

    list_node.clear()
    selected_records = [record for record in records if record.kind == "first-author"][:5]
    fragment = BeautifulSoup(build_selected_publications(records), "lxml")
    for child in fragment.body.contents if fragment.body else fragment.contents:
        if getattr(child, "name", None):
            list_node.append(child)

    changed = write_text_file(INDEX_HTML, serialize_document(soup))
    return changed


def update_figures_page(records: list[PaperRecord]) -> bool:
    html_text = read_text_file(FIGURES_HTML)
    soup = BeautifulSoup(html_text, "lxml")
    update_item_list_schema(soup, records)

    content_column = soup.select_one(".figure-page-layout .content-column")
    if content_column is None:
        raise RuntimeError("Could not locate figures content column.")

    first_author = [record for record in records if record.kind == "first-author"]
    count_label = small_number_label(len(first_author))

    for selector in [
        ('meta[name="description"]', "content"),
        ('meta[property="og:description"]', "content"),
        ('meta[name="twitter:description"]', "content"),
    ]:
        node = soup.select_one(selector[0])
        if node and node.has_attr(selector[1]):
            node[selector[1]] = re.sub(
                r"\b(five|5)\s+first-author",
                f"{count_label} first-author",
                str(node[selector[1]]),
                flags=re.I,
            )

    summary_node = soup.select_one(".figure-rail__summary")
    if summary_node:
        summary_node.string = (
            f"A visual guide to {count_label} first-author solar-physics papers. "
            "Each section shows one representative figure together with a short note on "
            "the science question and what the figure shows."
        )

    figure_index = soup.select_one(".figure-index--rail")
    if figure_index:
        years = [record.year for record in first_author]
        duplicate_years = {year for year in years if years.count(year) > 1}
        figure_index.clear()
        for record in first_author:
            item = soup.new_tag("li")
            link = soup.new_tag("a", href=f"#{record.page_id or f'paper-{slugify(record.title)}'}")
            link.string = figure_index_label(record, duplicate_years)
            item.append(link)
            figure_index.append(item)

    # Replace the showcase sections after refreshing the rail metadata above.
    showcase_sections = content_column.select("section.figure-showcase")
    for section in showcase_sections:
        section.decompose()

    link_section = content_column.select_one("#links")
    insert_before = link_section if link_section else None
    fragment = BeautifulSoup(build_figures_sections(records), "lxml")
    sections = [node for node in (fragment.body.contents if fragment.body else fragment.contents) if getattr(node, "name", None)]
    if insert_before:
        for section in sections:
            insert_before.insert_before(section)
    else:
        for section in sections:
            content_column.append(section)

    changed = write_text_file(FIGURES_HTML, serialize_document(soup))
    return changed


def update_sitemap(refresh_date: str) -> bool:
    if not SITEMAP.exists():
        return False

    from xml.etree import ElementTree as ET

    tree = ET.parse(SITEMAP)
    root = tree.getroot()
    ns = {"sm": "http://www.sitemaps.org/schemas/sitemap/0.9"}
    changed = False
    for url in root.findall("sm:url", ns):
        loc = url.find("sm:loc", ns)
        lastmod = url.find("sm:lastmod", ns)
        if loc is None:
            continue
        text = (loc.text or "").strip()
        if text.rstrip("/") in {
            SITE_BASE_URL.rstrip("/"),
            f"{SITE_BASE_URL.rstrip('/')}/publications.html",
            f"{SITE_BASE_URL.rstrip('/')}/figures.html",
        }:
            if lastmod is None:
                lastmod = ET.SubElement(url, "{http://www.sitemaps.org/schemas/sitemap/0.9}lastmod")
            if lastmod.text != refresh_date:
                lastmod.text = refresh_date
                changed = True
    if changed:
        tree.write(SITEMAP, encoding="utf-8", xml_declaration=True)
    return changed


def serialize_document(soup: BeautifulSoup) -> str:
    doctype = "<!DOCTYPE html>\n"
    output = str(soup)
    if not output.lstrip().lower().startswith("<!doctype"):
        output = doctype + output
    return output


def load_records_from_state(state: dict[str, Any]) -> list[PaperRecord]:
    records: list[PaperRecord] = []
    for entry in state.get("records", []):
        records.append(PaperRecord(**entry))
    return records


def records_to_state(records: list[PaperRecord], refresh_date: str, page_changes: dict[str, bool]) -> dict[str, Any]:
    return {
        "generated_at": dt.datetime.now(dt.timezone.utc).isoformat(),
        "refresh_date": refresh_date,
        "counts": {
            "all": len(records),
            "first-author": sum(1 for record in records if record.kind == "first-author"),
            "collaborative": sum(1 for record in records if record.kind == "collaborative"),
            "dataset": sum(1 for record in records if record.kind == "dataset"),
        },
        "page_changes": page_changes,
        "records": [dataclasses.asdict(record) for record in records],
    }


def append_update_log(records: list[PaperRecord], refresh_date: str, page_changes: dict[str, bool]) -> None:
    UPDATE_LOG.parent.mkdir(parents=True, exist_ok=True)
    with UPDATE_LOG.open("a", encoding="utf-8") as handle:
        handle.write(
            json.dumps(
                {
                    "timestamp": dt.datetime.now(dt.timezone.utc).isoformat(),
                    "refresh_date": refresh_date,
                    "page_changes": page_changes,
                    "records": [
                        {
                            "title": record.title,
                            "kind": record.kind,
                            "year": record.year,
                            "status": record.status,
                            "summary_source": record.summary_source,
                            "figure_source": "site" if record.figure_src else "pending",
                            "found": True,
                        }
                        for record in records
                    ],
                },
                ensure_ascii=False,
            )
            + "\n"
        )


def refresh_due(last_refresh_text: str | None, *, force: bool) -> bool:
    if force:
        return True
    if not last_refresh_text:
        return True
    try:
        last_refresh = dt.date.fromisoformat(last_refresh_text.strip())
    except Exception:
        return True
    today = dt.datetime.now(dt.timezone.utc).date()
    return (today - last_refresh).days >= 14


def read_last_refresh() -> str | None:
    if not LAST_REFRESH.exists():
        return None
    return normalize_whitespace(read_text_file(LAST_REFRESH))


def main() -> int:
    parser = argparse.ArgumentParser(description="Refresh the static site from the source CV.")
    parser.add_argument("--dry-run", action="store_true", help="Do not write any files.")
    parser.add_argument("--offline", action="store_true", help="Skip all network fetches.")
    parser.add_argument("--force", action="store_true", help="Ignore the 14-day refresh gate.")
    parser.add_argument(
        "--openai-model",
        default=os.environ.get("OPENAI_MODEL", "gpt-4.1-mini"),
        help="OpenAI model used for summary generation.",
    )
    args = parser.parse_args()

    if not CV_SOURCE.exists():
        print(f"Missing source CV: {CV_SOURCE}", file=sys.stderr)
        return 1

    last_refresh = read_last_refresh()
    if not refresh_due(last_refresh, force=args.force):
        print("Refresh skipped: less than 14 days since the last successful run.")
        return 0

    paragraphs = read_docx_paragraphs(CV_SOURCE)
    cv_records = parse_cv_records(paragraphs)

    current_publications = parse_current_publications(read_text_file(PUBLICATIONS_HTML))
    current_selected = parse_current_selected(read_text_file(INDEX_HTML))
    current_figures = parse_current_figures(read_text_file(FIGURES_HTML))
    previous_state = load_previous_state()

    openai_api_key = os.environ.get("OPENAI_API_KEY")
    records = merge_records(
        cv_records,
        current_publications,
        current_selected,
        current_figures,
        previous_state,
        offline=args.offline,
        openai_api_key=openai_api_key,
        openai_model=args.openai_model,
    )

    refresh_date = dt.datetime.now(dt.timezone.utc).date().isoformat()
    page_changes = {"index": False, "publications": False, "figures": False, "sitemap": False}

    current_publications_state = sorted_publication_state_from_current(current_publications)
    current_selected_state = selected_state_from_current(current_selected)
    current_figures_state = sorted_figure_state_from_current(current_figures)
    next_publications_state = sorted_publication_state_from_records(records)
    next_selected_state = selected_state_from_records(records)
    next_figures_state = sorted_figure_state_from_records(records)

    if not args.dry_run:
        if not state_equals(current_publications_state, next_publications_state):
            page_changes["publications"] = update_publications_page(records)
        if not state_equals(current_selected_state, next_selected_state):
            page_changes["index"] = update_home_page(records)
        if not state_equals(current_figures_state, next_figures_state):
            page_changes["figures"] = update_figures_page(records)
        page_changes["sitemap"] = update_sitemap(refresh_date)
        append_update_log(records, refresh_date, page_changes)
        write_text_file(LAST_REFRESH, refresh_date)
        write_json_file(SITE_STATE, records_to_state(records, refresh_date, page_changes))
    else:
        print(json.dumps(records_to_state(records, refresh_date, page_changes), indent=2, ensure_ascii=False))

    print(
        f"Refresh complete: {len(records)} records processed; "
        f"page changes={page_changes}; dry-run={args.dry_run}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
