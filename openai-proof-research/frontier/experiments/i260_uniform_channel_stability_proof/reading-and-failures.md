# I260 reading record and failures

## Fully read project inputs

- Root AGENTS.md and sources/upstream.json, completely.
- I262 target, all 205 lines, with detached SHA256 checked against both the assignment and I262 authentication.
- I262 input-authentication.json, completely.
- I250 derivation, all 168 lines, and its input-authentication.json, completely.
- I259 derivation, all 206 lines, its input-authentication.json and literature.md, completely. The final I259 portion was re-read separately after combined output truncation. These were prior derivation/source records, not a prior review result.
- sources/CONTENTS.md lines 6538–6575, family 262 and the three manuscript descriptions. A first overbroad catalogue output was truncated and was not treated as a full read; the relevant range was then read explicitly. sources/preprints-tree.json was searched only for the Lieb–Thirring manuscript paths, not read in full. sources/tree.json was not used.

## Independently retrieved primary reads

- Pinned equality manuscript build/sections/introduction.tex, all 161 lines, retained as equality-introduction.tex. Includes Theorem thm:main, conventions, quantitative-defect discussion and source limits.
- Pinned matrix companion build/sections/introduction.tex, all 106 lines, retained as matrix-introduction.tex. Includes Theorem thm:main, conventions and proof-strategy description. Neither underlying upstream proof was audited. No contribution-overlap conclusion was made.
- HLW author-hosted PDF pages 3–6, every paragraph, displayed formula and page-5 footnote, visually read from rendered source excerpts. This includes operator/form conventions, Theorem 3.1, Definition 3.2, Lemma 3.3 and its proof, Lemma 3.4 and its proof across pages 5–6, and the complete presented Theorem 3.1 proof in Section 3.3. The opening two lines of Section 3.4 on page 6 were read but not used. Pages 1–2 and 7 onward were not read or retained. Full PDF bytes were held in memory for SHA256 authentication and rendering selected pages; no complete unread PDF was written.
- Carlen–Frank–Lieb arXiv HTML 1301.5032v2, lines 35–100 inclusive, fully read: bibliographic information, introduction, Section 2.1, Theorems 2.1 and 2.2. Later proof sections were not read and are not dependencies. It is credited prior art only.

No other external theorem is used. Leng 2606.03749 and MathDB appear in historical source records only and were not independently fetched for this correctness task. No significance score is inferred.

## Retrieval and tool failures

- Initial web open of the HLW primary PDF returned: `Failed to fetch https://www.ma.imperial.ac.uk/~alaptev/Papers/hlw.pdf: (400) Timeout fetching`. Direct HTTPS retrieval succeeded, and its hash matched I259.
- An attempted in-memory PDF page extraction found `ModuleNotFoundError: No module named 'pypdf'`. No package was installed. Installed Poppler pdftoppm rendered selected pages directly from full PDF bytes on standard input. Four rendered primary page excerpts are retained in the assigned source directory, not browser or repository snapshots.
- A path-discovery query for frontier/sources/i250_lieb_thirring_transverse_hessian returned no such directory. The actual I250 authentication record was subsequently read and its precise pinned URLs used. No unlocated source was treated as read.
- Combined reads exceeded an output budget once; relevant tails were re-read in bounded commands. Nothing hidden by truncation was accepted as evidence.

The PDF skill was read only for the source-rendering workflow. No PDF was authored or edited and no skill authorization gate was invoked. The user-specified write scope overrides its generic temporary/output-directory conventions.

## Scope compliance

No subagents or additional threads were started. Runtime identifies GPT-6.1 Sol with high reasoning effort; no provider/model change was made. Standard was the requested service tier; the tool surface did not independently expose a service-tier field, so this record does not fabricate a tier verification.

No other review, live sibling material, or live I256–I258 output was read. No snapshots, giant history replay, research code, tests, numerical experiments or scans were run. Ephemeral Python was limited to retrieval, extraction/rendering orchestration and provenance hashing. No shared edit, index edit, staging, commit, publishing, or count increment occurred.

Writes are limited to the assigned review, analysis, reading record, authentication JSON, literature record and fully read primary excerpts within the assigned source directory. The final handoff supplies detached hashes, including the authentication file itself, avoiding a circular self-hash.
