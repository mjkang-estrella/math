# Retained limitations and helper failures

- Initial combined instruction/reservation output was truncated by the tool. Reservation keys, prior coverage, exact reserved old rows and relevant old notes were then read with bounded structured selections.
- Initial assumption historical-depth-r8/r10 existed was wrong; filename search located fresh-corpus-r8/r10. Their immutable tree/receipt hashes were verified before reuse.
- BeautifulSoup was unavailable (`ModuleNotFoundError: No module named bs4`). No package installed. Built-in html.parser produced local text extracts instead; retained original HTML bytes remain the authority.
- HTTPS AIM hostname verification failed. No certificate override or subsequent AIM hostname request.
- Workshop-report PDF, Citeseer PDF, and two CMU author-PDF paths returned404. Their actual URLs, dates and statuses are in receipts. No source body or invented hash attributed to these failures.
- Full dependency proofs and original AIM context are not cleared by related source fetches. Decimal diagnostics are not Lean or rigorous numerical certificates.
