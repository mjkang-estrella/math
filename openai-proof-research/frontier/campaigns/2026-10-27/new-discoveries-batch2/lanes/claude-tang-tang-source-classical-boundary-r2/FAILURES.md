# Preserved failures, limitations and procedural deviations

Access failures (single attempts, not retried):
- `https://www.columbia.edu/~wt2319/`: HTTP 403 with a Cloudflare "Just a moment…" challenge page (5526 bytes, saved under downloads/wenpin-home/). STOP. No other Columbia host, no Academic Commons, no retry.
- `https://www.math.ucla.edu/~tml/`: HTTP 404. No alternate UCLA path was guessed.
- OpenAlex `filter=doi:…|title.search:…` returned HTTP 400 because the query was malformed. It was replaced by a plain search query. Not an access denial.
- Publisher full text (Project Euclid PDF advertised by OpenAlex and Semantic Scholar) was deliberately not followed. The same publisher returned an Incapsula challenge to the prior lane. Published problem text is unread.
- Inherited and unchanged: the BNF.pdf (Schilling–Song–Vondraček) timeout from the prior lane was not retried. No complete-Bernstein book body was read. Lamperti 1958 and James 2010 were used instead.

Scientific limitations:
- Liggett 2018 manuscript unread; no absence claim.
- Lamperti 1958 was read via pdftotext OCR, and formulas (1.4) and (3.17) are typographically garbled. The α = 1/2, δ = 2/3 specialization was confirmed only by consistency with James (1.1)/(2.6) and by numerical diagnostics.
- The citer screen is at title level, except for the one body scanned (1804.07696v2). Not exhaustive.
- Current public proof-registry heads were not checked (held, per instructions).
- The first arXiv keyword query returned off-topic results (astrophysics, nanotubes), apparently from arXiv phrase parsing. They are preserved as returned and no inference was drawn.

Procedural deviations from "all helpers and hashes via helper_guard":
- Two `sha256sum` invocations ran natively, outside the guard: (1) re-verifying the reused frozen 1908.10024v1 and 1607.03036v1 files; (2) hashing the three extracted text files. Also native: a few `grep`/`sed` bounded reads and `mkdir`. Every Python run, retrieval, pdftotext extraction, freeze, check, finalize and verify ran under the guard. The hashes are recomputed under the guard in manifest.json.
- The lane directory was created natively with `mkdir -p` before the guarded freeze.
