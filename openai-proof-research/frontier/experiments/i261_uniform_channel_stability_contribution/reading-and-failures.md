# I261 reading extent, failures and write discipline

Date: 2026-10-12. Contribution/primary-overlap review of I262 only. User requested GPT-6.1 Sol/high/Standard; runtime identifies gpt-6.1-sol/high. No provider/model change or delegation occurred. Service tier was not independently exposed by the runtime, so Standard is not claimed as separately verified.

## Local reads

Fully read: AGENTS.md; sources/upstream.json; I262 target; I262 input-authentication.json; I250 and I259 iterations; I250 and I259 input-authentication.json; I259 literature.md. The target SHA256 matched the exact supplied identity at first read and was checked again at manifest creation. The I262 listed local input hashes were checked against actual bytes. Nothing from I256–I258 or another review was read.

sources/CONTENTS.md was initially requested too broadly and the returned catalogue text was truncated. It was not fully read, and no unrelated catalogue passage is evidence. A bounded family-262 extraction (lines 6538–6573) was then read. sources/preprints-tree.json was parsed only to locate the three relevant preprint families' .tex paths; no full-tree content read is claimed. There was no git history replay, live sibling read or snapshot operation.

## Primary reads

Exact extents and labels are listed in literature.md and the authentication manifest. Five equality sections and five matrix sections were fully read, with truncation repaired by focused follow-up reads where necessary. The matrix trace and path prefixes were read only up to the first proof. The scalar introduction and the two matrix/equality bibliographies were fully read. The remaining appendices, preambles, histories and unlisted proof sections were not read.

HLW PDF pages 3–6 were rendered by pdftoppm and all text and formulas were visually inspected with view_image. That includes the operator conventions and the complete presented Theorem 3.1 proof, not just its statement. The full PDF was fetched only into memory to hash and extract; it was not retained. Four rendered page excerpts were temporary within the assigned source directory and removed after inspection. No PDF pages outside 3–6 were read. Original short reading notes replace those page reproductions.

CFL Sections 1–2 were read through the main stability statements, viewpoint, auxiliary theorems and the proof of Theorem 2.2. Section 3.1's remainder statement and presented argument were read; later 3.2 was only partially exposed and is not a dependency. Some Section 4 passages were exposed while navigating; no complete Section 4 read is claimed. Entire Section 5 was subsequently extracted using intact MathML alttext and read through the end of Lemma 5.3's proof. Section 5 is the primary local-stability-method comparison, not a matrix theorem.

Leng's introduction, spectral Theorem 1.2 and the complete spectral proof through its end were read; interspersed convex-geometric statements were visible but their later proofs were not read. FGL arXiv PDF pages 5–10 were fully extracted and read, including all Section 2 main statements through Theorem 5 and the beginning of Section 3. Proofs elsewhere were not read or used.

## Retrieval/extraction failures and corrections

- Web opening the author-hosted HLW PDF returned `Internal Error` twice. Direct urllib retrieval succeeded and reproduced I259's SHA256. No hypothesis was inferred from a search snippet or damaged text extraction.
- The first in-memory render attempt failed with `ModuleNotFoundError: No module named 'fitz'`. Existing pdftoppm succeeded; no dependency installation was performed.
- A BeautifulSoup extraction attempt failed with `ModuleNotFoundError: No module named 'bs4'`. Standard-library HTMLParser plus MathML alttext produced intact CFL Section 5 mathematics. This was text extraction only; no research program was written or executed.
- Direct urllib retrieval of the FGL journal-hosted PDF returned `HTTP Error 403: Forbidden`. The web tool could expose that PDF, but the actual hashed/extracted document used here was the arXiv PDF. Its separate identity is recorded.
- Some initial tool output batches were truncated. Critical theorem statements, equality action and rigidity, matrix introduction, field ending and CFL Section 5 were reread in bounded outputs. No unread source was retained as a fully read excerpt.

## Written paths

Only these assigned files remain:

- frontier/reviews/i261-uniform-channel-stability-contribution.md
- frontier/experiments/i261_uniform_channel_stability_contribution/analysis.md
- frontier/experiments/i261_uniform_channel_stability_contribution/reading-and-failures.md
- frontier/experiments/i261_uniform_channel_stability_contribution/input-authentication.json
- frontier/sources/i261_uniform_channel_stability_contribution/literature.md
- frontier/sources/i261_uniform_channel_stability_contribution/equality-main-excerpt.tex
- frontier/sources/i261_uniform_channel_stability_contribution/equality-action-excerpt.tex
- frontier/sources/i261_uniform_channel_stability_contribution/matrix-main-excerpt.tex
- frontier/sources/i261_uniform_channel_stability_contribution/classical-primary-excerpts.md

No shared files, indexes or proposals were edited. No staging, commit, publishing, tests, numerical experiments/scans, research code or subagents were used. Retrieval/extraction and provenance-hashing snippets ran in memory and were not saved. Detached artifact hashes are in input-authentication.json; that manifest's own detached SHA256 is reported at handoff to avoid self-reference.

## Gate limits

TECHNICAL is a contribution judgment supported by an independent alternative threshold derivation. It is not a full proof review of I262's displayed constants or analytic perturbation lemmas. No author rebuttal or repair was requested. No exact duplicate and no absence theorem were established. All three candidate versions remain one finding; no acceptance count changed.
