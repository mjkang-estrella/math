# Provenance and validation boundaries

This is an author manuscript package, prepared for Myeongjin Kang by the assigned GPT-6 Astra/high manuscript author agent at normal speed. No subagents were started. Only this package was edited; no shared/frozen source was changed, staged, committed or uploaded. The parent retains integration and acceptance authority.

## Fixed mathematical object

The source input is OpenAI Math revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. AGENTS.md requires treating its theorems as true and independently validating new deductions rather than auditing upstream truth. Source298 supplies a bounded embeddable n=2^64+1 tuple X=C+sqrt(h)S with h>0, finite Fisher information, and finite gap at least 1/2. The target is exactly two bounded self-adjoint elements with -infinity < chi < chi* < infinity, original cutoff/ordinary limsup, no conditioning and no ultrafilter. The source-specialized stronger transfer is retained. No W*-generation assertion was added.

## Frozen anchors

- Author r104 manifest: `b6c525288bd6a7203d13c8b8ed4b696e14a0f8c3a06cd30cb6fbe871d6dfbeb3`.
- Candidate: `ed09eaca101d308384672977a8a9df9e37445c82f7d1fdabab528465ce158cb6`.
- Scope: `8e9b3f5f30e02e91e8e49010350c07bb8dff845c806e506e8e5b598bed37589e`.
- Full proof review r2 manifest: `eb7f9e3cb4c14ad5793906ff0f3f5b7288e8bfebc5cc72a0e160fcd6c7fdf87c`, verdict PASS_FULL_T298P.
- Contribution review r2 manifest: `31e84ba9937ddd232381af31d869f471b911e124cf786b43179c693e81576566`, SUBSTANTIAL conditional on correctness, with four required attribution items now mapped in required-item-map.md.
- Attribution r1 manifest: `27a968a7dcb796907e97e4d4c39a2bd0e978a0118fb3d05d2f51eb1671a5d6e3`.
- Attribution r2 manifest: `6c77938d8f46ef62dd2523dc4df749539ec22e45b4fa184e2a41516ba1a102a8`.
- Formal r1 manifest: `e8d1d16e4d90b53b9fbb2b469a40e63c1d8b1e67b3647448f37f33b0b1857400`.

The author verifier was read and executed with its external manifest anchor: PASS, 20 public payloads, 19 canonical source blobs, three primary PDF/text pairs. All five other frozen manifest anchors above were recomputed and matched. `inputs.json` records exact external file hashes, including upstream provenance, reviews, addenda, formal source/coverage, and existing private primary copies. Hash authentication does not imply a whole-file reading; reading-limits.md distinguishes the two.

The proof review's explicit completions were integrated into the actual proofs. A normalization omission in one prose equation of that review was not copied: manuscript equation (33) includes epsilon² k⁴ in the denominator. The final draft uses a path as the permitted spanning tree and fixes a real orthonormal normal basis. This is a concrete instance of the reviewed construction, not a change of target.

## PDF operation and reproducibility

The required PDF skill was read. Immediately before the first authoring command, exactly one successful marker was run:

`node container_tools/mark_artifact_operation_started.mjs --operation-kind create --expected-output-count 1 --output-format pdf`

Working directory: `/home/mj-kang/.cache/codex-runtimes/codex-primary-runtime/plugins/openai-primary-runtime/plugins/pdf/skills/pdf`.

The repository's existing LaTeX/Tectonic workflow was used for the mathematical paper. Initial builds exposed two hbox overflows, which were corrected in prose and by a modest emergency stretch. The final build has no warnings and no unresolved references. All 18 pages were rendered with Poppler at 90 dpi and individually opened for visual inspection. The final PDF has no clipping, overlapping formulas, missing glyph boxes or broken page numbering observed. The final reference page has two entries with ordinary whitespace. A fresh second build from the complete source produced an identical PDF hash.

## Formal, numerical, and review limitations

The formal source and coverage were read. Four support declarations and four controls are explicitly scoped; no free-entropy existence or analytic limit theorem is formalized. No independent formal-review pass was assumed in the manuscript. The parent reported that a first independent formal audit process failed before a verdict and that a fresh audit was running; this manuscript does not rely on its outcome. Any later formal-review result cannot enlarge the explicit coverage.

The prior finite diagnostics were inspected as finite checks only. The new local arithmetic script is likewise finite support only. Its controls do not validate analytic adjoint domains or asymptotic volumes. The new integrity verifier is read-only and externally anchored; its copied controls test its failure modes, not the mathematics. The proof and contribution verdicts concern the exact frozen candidate, while the new manuscript needs its own independent review. No acceptance or result count is changed by this package.

## Integrity-control development note

The first control invocation redirected its output directly to a new sealed-directory receipt, so shell redirection created an unexpected empty public file before the positive copied-tree case. Exact membership correctly rejected it. The empty receipt was removed, the unchanged controls were rerun with output under excluded `tmp/`, and the successful result was then copied into `validation/` before the final seal. No verifier defect or mathematical issue was involved. The final seal was independently checked and its controls replayed with transient output.

## Parent revision after independent manuscript review r3

The r1 paper and all prior independent packets remain byte-identical. The parent implemented the two required r3 findings in a new r2 source: an explicitly derived bilinear coefficient-score convention with Hilbert-adjoint conversion and finite Neumann-sum limit passage, and the finite-real/standard-axiom/trusted-cache disclosure. It also fixed the output-microstate notation and updated the scoped formal status. These are authored repairs awaiting a fresh independent manuscript verdict. The corrected score diagnostic is copied from the independent r3 review with credit; it verifies finite pairing cases only. No new upstream theorem or literature-priority claim is introduced.
