# Actual source and reading inventory

All twenty raw JSONL records were extracted byte-for-byte with final newline. raw-records.json stores the full parsed objects, chunk SHA, one-based line and raw SHA. results.json additionally records each literal UTF-8 statement SHA. No reservation selection occurred.

All 18 distinct assigned arXiv abstract/history pages returned 200. All 35 versions listed on those pages were downloaded as PDFs and converted with pdftotext. versions.json records their version numbers; sources/abs-receipts.json and sources/pdf-receipts.json record exact URL, UTC, HTTP status, body SHA and destination. Text artifacts and all scripts are covered by manifest.sha256. A downloaded body is not equivalent to a read body.

Actual selected target passages and neighbouring definitions are listed separately in each result. focused-version-passages.txt and statement-passages.json preserve automatically located contexts and hashes, including no-match diagnostics; the broader version-target-passages.txt is not a proof-audit certificate. Manual follow-up located v1 matroid Conjecture 1.9 (v2/v3 1.2), v1 involution Conjecture 5.9 (v2 5.6), Currie v1/v2 Proof of Conjecture 1 (v3 Theorem 16), Elizalde v1 Corollary 3.3 (v2 4.3), Ohsugi Conjecture 4.3, and preconditioned QC v1 Conjecture 10 (v2/v3 9). Some generated contexts match references rather than the actual target; do not infer full reading from that output.

Additional primary bodies fetched and selectively read:

- Ayyer–Strehl 1008.2134: Theorem 4 product and ratio, Theorem 8 triangularization and Proposition 7 proof. These settle 319080. Not all general model definitions or entire journal history audited.
- Dobson–Ortner–Shapeev 1004.3435: formulas (12)–(13), Theorem 2 and complete local similarity proof, condition-number section routing. This is periodic, so the Dirichlet bridge is explicitly worked in ORDINARY-ATTEMPTS.md. No claim that its abstract alone proves the assigned records.
- Goff, Integers 13 (2013) A42: actual journal introduction, definitions, selected region lemmas, Section 7.2 printed peanut recipe and formula. Exact ordinary recount supplied. Not the entire lengthy superregion classification proof, unnecessary to the already printed counterfamily exclusion.
- Stack-number is not bounded by queue-number, journal body: subdivision conjecture/counterfamily paragraph and fixed-depth recipe. Not its entire unbounded-stack proof audited; it is a published theorem used for exclusion, not a new deduction credit.
- Fischer–Romik 0903.5073: exact signed extension equation (7), Theorems 1–2, boundary formulas and near-symmetry exceptions. No full proof audit of monotone-triangle polynomial identities.
- Karklinsky–Romik author revised body: Conjecture 2 and nearby proved upper-triangle formula. It does not by itself prove the extension.

Koda–Sato–Takegahara: primary abstract found by web search reports an affirmative answer to the Kim–Kim conjecture. Direct body retrieval returned 503; later web retrieval returned 429. No further attempts or alternate route. The exact full theorem and proof remain unread. Search result is a lead, not an exact-source outcome certificate.

Journal version histories, all corrections/withdrawals, all citing primary proof bodies and all illustrated objects have NOT been exhaustively reviewed. No visual figure reconstruction is claimed. The cube attempt needs an all-realizations graph/face bridge and already instantiates a printed necessary condition. No candidate is proposed and no source-eligible mechanism is certified.

Primary retrievals used lawful public HTTP with ordinary certificate verification. No GitHub API access; no browser/account actions. Fetch jobs used two threads, CPU limit 120 s and address-space limit 6 GiB; completed runs were well under 140 wall seconds. Scripts and receipt output are retained. No numerical/solver/formal execution.
