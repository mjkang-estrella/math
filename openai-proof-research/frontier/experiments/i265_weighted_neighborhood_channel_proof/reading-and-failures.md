# I265 read extents, failures, and scope

This is an independent correctness review of the stronger I264 weighted-neighborhood theorem, not a repeat of I260. Verdict: PASS with no required repairs. Candidate identity: SHA256 `a0080234eacf4d410917e426222e3e89b24f9eba968cc815c4b46c5b59957395`, 223 lines, 10,230 bytes. No author response or prior I264 gate was presumed.

## Completely read project records

- Root `AGENTS.md` and `sources/upstream.json`.
- `frontier/iterations/i264-weighted-neighborhood-channel-stability.md`, all 223 lines, independently hashed before review and again at completion.
- I264 experiment `analysis.md` (36 lines), `reading-and-failures.md` (11 lines), `input-authentication.json` (69 lines), and source `literature.md` (9 lines), completely.
- Finalized `frontier/reviews/i260-uniform-channel-stability-proof.md` (131 lines), and its experiment `analysis.md` (58 lines), `reading-and-failures.md` (36 lines), `input-authentication.json` (185 lines), and source `literature.md` (22 lines), completely. This permitted prior correctness review was background, not a substitute for proving the stronger theorem's new estimates. No other review output was read.
- `sources/CONTENTS.md` lines 6538–6573 only, including family 262's manuscript descriptions. An initial overbroad catalogue output was truncated and was not treated as a complete catalogue read. The relevant range was subsequently read separately. `sources/preprints-tree.json` was searched only for the two exact primary introduction paths; matching entries were at lines 35257 and 68875. `sources/tree.json` was not used.

Checked for additional `AGENTS.md` files on the assigned frontier/reviews, frontier/experiments, and frontier/sources ancestor paths; none were present. The newly created assigned directories did not previously exist. The source catalogue and path listing are navigation records, not theorem evidence.

## Fully read primary excerpts and authentication

- Equality manuscript `build/sections/introduction.tex`, all 161 lines, from the pinned revision. It includes the complete Theorem `thm:main`, form and trace conventions, equality profile, single scalar eigenvalue, quantitative-defect discussion, and references. No proof beyond the introduction was read or audited.
- Matrix companion `build/sections/introduction.tex`, all 106 lines, from the same pinned revision. It includes complete Theorem `thm:main`, measurable finite-matrix hypotheses, constant, optimizer, trace conventions, and proof-strategy summary. The referenced external history input was not expanded or read; it is not a correctness dependency.
- HLW primary PDF rendered pages 3, 4, 5, and 6, each completely and visually read from the finalized I260 retained primary excerpts. Page 3's form/operator conventions, Theorem 3.1, Definition 3.2, Lemmas 3.3 and 3.4 and their proofs, the page-5 footnote, and the complete Theorem 3.1 proof in Section 3.3 were read. The two opening Section 3.4 lines on page 6 were read but are unused. Pages 1–2 and 7 onward were not read or retained.

All three original primary URLs were freshly retrieved over HTTPS into memory, solely for source identity checking. Both complete TeX section bytes match the corresponding fully read I260 source excerpts. The full HLW PDF byte hash matches the I260 provenance identity. The four read rendered pages also match the exact individual hashes recorded by I260. The fully read TeX sections and four fully read page images were then copied individually into the assigned I265 source directory. No whole source tree, full unread PDF, or unread paper section was copied. No fresh PDF rendering was needed; no artifact skill was invoked.

Carlen–Frank–Lieb, MathDB, and other historical literature mentioned in input records were not independently read in I265, are not correctness premises, and support no novelty conclusion here. The exact pinned theorem contracts and external endpoint are the only primary mathematical dependencies.

## Tool and retrieval failures

- The first combined catalogue/candidate output was truncated because the catalogue was too large. The candidate was then read completely in a bounded command, and the relevant catalogue range separately. A later combined primary/I260 output also truncated a middle part of the I260 review; that review and its analysis were re-read completely in separate bounded commands. Truncated material was never treated as read.
- The web tool opening the author-hosted HLW PDF returned `Failed to fetch https://www.ma.imperial.ac.uk/~alaptev/Papers/hlw.pdf: (400) Timeout fetching`. Direct HTTPS retrieval succeeded, returning 1,192,425 bytes with the expected hash. No source claim was based on the failed web output.
- A bounded existence check for the three future I265 artifact paths returned no matches and exit code 2 because they were absent. This was an ordinary pre-write check, not a missing mathematical input.
- An optional analysis edit initially failed its patch-context match because a paragraph fragment was supplied as an entire line. The failed patch made no change; the intended explicit-constants block was then added with the correct section context.

No failed request was treated as proof evidence. No package was installed and no source identity mismatch occurred. Source retrieval and hashing were the only computational operations beyond file inspection and artifact writing.

## Scope and runtime

The T3 thread configuration independently reports model `gpt-6.1-sol`, reasoning option `high`, and service tier option `default` (Standard). Runtime mode is full-access; no provider/model/options change was made. No subagents or new threads were launched.

No live sibling material, I261 files, other current gate, or other review was read or inferred. The only prior review read was the specifically authorized finalized I260 record. No shared ledger or candidate was edited. No staging, commit, publication, research code, test, numerical experiment, scan, snapshot, or giant history replay occurred. Ephemeral Python was restricted to retrieval, copying individually fully read excerpts, writing the provenance manifest, and hashing. All working directory and output paths are inside this project.

Writes are exclusively the assigned review, analysis, reading record, authentication JSON, source literature record, and six individually fully read primary excerpts under `frontier/sources/i265_weighted_neighborhood_channel_proof/`. The authentication file lists other output hashes without self-reference; its detached hash is supplied in the final handoff. No contribution, acceptance, or count verdict is assigned.
