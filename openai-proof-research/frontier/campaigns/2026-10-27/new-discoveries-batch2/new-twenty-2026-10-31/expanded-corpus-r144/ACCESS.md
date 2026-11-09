# Access and review boundaries (2026-11-04 UTC)

Primary arXiv bodies for all twenty records were fetched through their ordinary
abs and pdf URLs. Status/bytes/hash/date receipts are retained. No arXiv search
API, Crossref, Semantic Scholar API, ScienceDirect access route, TLS-disable
option, challenge bypass or browser tab was used.

The web connector could not fetch the DOI redirects for the 2021 Li–Weng journal
paper and the 2024 Weng paper, reporting non-retryable inaccessible/unsafe-to-open
redirect errors. Those routes were not retried. The corresponding current
arXiv PDFs were read instead; the published 2021 body has not been compared.
Both available versions of the actual 2004.06285 arXiv source were inspected;
the target remains in v2.

The ETH URL https://people.math.ethz.ch/~lgishboli/rem_threshold.pdf returned
HTML rather than PDF. Its bytes and headers are retained under rem-threshold.*.
It was not retried. The exact current resolution of 350736 is explicit in
Corollary 1.2 of arXiv:2609.20237, whose primary body was read.

The AIMS 2025 article's HTML did not expose its full body through the connector.
Its explicit public PDF URL was found by search, downloaded with verified TLS,
and its theorem/example/proof bodies inspected. This was not a denied route.
The 2018 introductory and 2023/2024 companion arXiv PDFs were also inspected.

Web searches were bounded discovery aids, not systematic bibliographic coverage.
Relevant queries included the exact phrase "rainbow vertex-disconnection"
with "counterexample", "Conjecture 6.12", "Nordhaus", "2026", and "thesis".
They returned the original source and the 2018, 2023/2024 and 2025 papers,
but no explicit prior refutation. No institutional thesis clearing claim is made.

Registry receipts are in sources/*head*, *root*, omega-d5.json,
omega-problems.json and openai-preprints.json. Complete subtree path screens
were used after detecting truncation in root recursive trees. No target-related
path was identified; this is not an audit of all their theorem bodies.
