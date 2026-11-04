Hello, welcome to my website creation adventure:D

The root HTML files are the current website. Refresh their publication content with:

```sh
python scripts/update-site.py --offline --force
```

`automation/source/publication-records.json` is the reviewed bibliography from the November 2026 CV. Edit it when adding or removing papers. `data/publication-overrides.json` holds corrected metadata, links and concise summaries. The DOCX is retained as a fallback source; the downloadable PDF is in `documents/`. The figures sidebar groups papers by year and preserves individual paper anchors.
