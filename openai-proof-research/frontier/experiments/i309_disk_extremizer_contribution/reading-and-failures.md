# I309 — reading, searches, failures, and operational limits

2026-10-13. Work stayed inside `/home/mj-kang/Documents/Dev/math/openai-proof-research`. Only the five assigned outputs were authored. No subagents, live sibling reads, shared-index changes, git commands, publication, messages to outsiders, numerical scans, or giant history replay were performed. The count remains thirteen. No qualitative or quantitative proof pass is assumed.

## Local reads and authentication

Read AGENTS.md and sources/upstream.json first. The pin is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; upstream theorem truth is stipulated. The initial CONTENTS.md display was overlarge and truncated; I subsequently confined catalogue reading to the Crouzeix entry and do not claim full catalogue reading. An initial filename search returned names of archived AGENTS/upstream files; their bodies were not read. It did not search for or open I308.

Read the three frozen candidates and their authentication records. Recomputed each candidate digest and every whole-file/passage digest declared by those records; all matched. Recomputed support-file digests without confusing hashing an unread whole file with substantive reading. Read I306/I307/I310 fully, the parent literature note, R019, I292 review and full analysis, R016, I246 review and full analysis, and their completed parent dispositions. Read actual direct-source theorem and ordered-test/positive-block passages. Exact local extents and digests are in input-authentication.json.

## External search routes

Bounded query groups covered: Crouzeix's 2004 analytical-function paper; Drury norm refinements involving f(0); disk scalar Schur equality and spectral zeros; nilpotent extremal Blaschke/monomial functions; almost-inner polynomial stability; quantitative nilpotent power gaps; and Gau–Wu equality/stability. A later group tested whether the quantitative modulus was already supplied by old nilpotent Schwarz–Pick results or published equality stability.

Examples of the actual queries were `Crouzeix "Bounds for analytical functions of matrices" pdf`, `"Crouzeix" "extremal" "zeros" "eigenvalues" disk`, `"nilpotent" "extremal" "Blaschke" numerical radius monomial`, `"almost inner" "polynomial" monomial stability`, `"numerical radius" "f(0)" "norm" Drury 2011`, and `"Gau" "Wu" "Inner functions of numerical contractions" stability quantitative`. Query absence is not the verdict. A search found the actual Gau–Wu institutional journal PDF; it was then retrieved and read at theorem/proof scope. The decisive comparison rests on that article, not the snippet.

Primary mathematical reliance is limited to the actual manuscript passages listed in literature.md. Secondary search results, third-party text reproductions, numerical-search papers, lecture listings, and catalogues were used only to locate primary sources. No empirical matrix optimization or other numerical scan was run.

## Successful reading and truncation repair

ACV v3: raw in-memory HTTP retrieval matched the existing prior-review raw digest; read Sections 9–11. The first combined display was truncated, so I separately read Section 9's opening and Section 11's middle. KMR v1: independently read Sections 2–5 and its introduction; Section 4 was reopened in full to ensure no quadratic-proof case was skipped. The parent note was treated as a lead.

Gau–Wu: successful institutional final-journal PDF, ten pages. Extracted text using `pdftotext -layout - -` from response bytes in memory. A combined PDF/web result truncated central text; I reread PDF pages 5–9, printed pp. 2186–2190, closing the necessity-proof gap. The entire substantive article and references were then available and read. Raw PDF, extracted whole-text, and page hashes are recorded. No new PDF/text body or section file was saved.

Crouzeix 2016: read the actual scalar extremal discussion and all Section 10, with its opening factorization reopened. Gaaya v1: read the model-space definitions and Section 4's nilpotent Schwarz–Pick statements and proof. Its contraction hypothesis was retained. No whole-paper reading is inferred from raw hashing.

## Failed or uncompleted access

- The first in-memory HTML extraction attempt failed before retrieval because `bs4` was unavailable. I used Python's standard-library HTMLParser instead; no package installation or extra script file was needed.
- Web opening the Rice lecture bibliography returned `(502) Bad Gateway`; direct Python retrieval raised `SSLCertVerificationError`. The author homepage `https://perso.univ-rennes1.fr/michel.crouzeix/` returned HTTP 403 (1,181 response bytes, SHA256 `ddf1eff6c6b41a269b87138db3ff31659003e8b146cf2e8765f650d2dfc1c706`). The publisher DOI web open returned `Internal Error`. The original Crouzeix 2004 full proof was not obtained. Its relevant theorem scope is credited through actual primary later formulations, not through an unread original proof.
- `https://centaur.reading.ac.uk/114467/1/main.pdf` returned an anti-bot HTML page (`Oh noes!`) in the web tool. No full reading of that manuscript is claimed.
- Web access to `https://par.nsf.gov/servlets/purl/10232251` returned `Internal Error`. A subsequent Python in-memory retrieval succeeded: HTTP 200, 187,039 PDF bytes, SHA256 `7438202c19a884ee16c508310f15e9f8d93aa3fde8ebc7b4bd8d14dfdb76c1ba`; extracted text SHA256 `429e84b583ac4bf1d25ba3915ea89ff7ba5a9040b1388c77fde9d2f3dcea63ed`. Searches for two anticipated section headings did not match. No substantive section from that PDF was read or relied upon; this was not treated as evidence of a missing theorem.
- Original Berger–Stampfli, Drury, Crabb, Sarason and Okubo–Ando full papers were not separately retrieved. Their relevant methods were assessed through the actual KMR and Gau–Wu proofs; no original-paper reading is claimed by citation inheritance.

## Contribution/proof boundary

The exact result is a routine minimal-polynomial consequence of the older all-H∞ model-summand theorem. The quantitative result was **not** dismissed on that basis alone: analysis.md explicitly traces the proposed D_L and exponent through the source block inequalities, autocorrelation endpoint deletion, and finite evaluation bound. It distinguishes those operations from ACV output-block/measure stability and from Gaaya's contraction theorem.

This is a contribution review. I308 remains unread. Q310 needs its own proof audit if the package is pursued; none is replaced by the scope calculation here. No worldwide-priority claim, no R019 reaward, and no extra I306/I310 slot is authorized. Detached hashes are returned for the five authored outputs; no self-referential output manifest was added.
