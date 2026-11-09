# Failures and deviations (preserved, not erased)

1. Custody ordering: the cached predecessor texts sol-hankel-breadth-depth-r1/sources/berg.txt and fq.txt were read natively before their hashes were recorded. Hashes were bound afterward in reference-bindings-supplement.json. Both PDFs (berg.pdf, fq.pdf) match the inherited receipt SHA256s. Theorem 4.2 was re-extracted independently from the hash-matched PDF (derived/berg-own-extract.txt).
2. Semantic Scholar: an arXiv-id lookup for math/9905079 returned 404. A later search query returned 429 at 2026-10-30T07:38:01Z. The host was stopped for this lane (stopped-hosts.json) with no retry.
3. zbMATH Open: the `ci:0994.11011` cited-by query returned a 404 "No results found" body. That is not a denial; it was not retried with variant syntax. zbMATH record contents are license-restricted.
4. The OpenAlex full-text search returned mostly series identities, and the arXiv "Filbert" search was dominated by an author surname. Both are coverage limits, not clearance.
5. The checker was extended in place (via a guarded Python edit) to add the denominator-law check before the final run. Only the final run's output is in check-results.json.
6. Not re-read in this lane: Guo–Zeng 1101.0983 (relied on inherited reading, non-decisive here) and the Szegő/Chihara CD textbook bodies.
7. Inherited denial routes (GitHub API/raw/codeload/diff/patch, ScienceDirect, Google challenge) were not attempted. The fetcher refuses them by construction.
