# Preserved failures / access limits

1. Initial guarded index parser attempted import bs4, which is unavailable:
   ModuleNotFoundError. Exit1. Replaced with bounded standard-library parsing;
   no installation, cap raise or bypass. Original tool output remains in session.
2. Bing RSS exact-phrase queries returned unrelated general-word results,
   including irrelevant adult results for the dihedral query. Raw responses are
   retained search-0..3.xml. No result destination was opened; no clearance.
3. Crossref bibliographic queries returned unrelated records; fourth request
   returned HTTP429. Exact failure URL is retained in failures.jsonl. No retry.
4. Guessed HMT tossa8.pdf returned404 before using the explicit volume-index
   tossa6.pdf link. Both events retained; no repeated inaccessible-interval loop.
5. No complete current public registry or all-citation history could be cleared
   inside inherited denied routes. This is an eligibility limit, not proof of
   absence. No forbidden route attempted.
