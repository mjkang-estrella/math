# Selection, provenance and scope

`selection.json` is the explicit source-to-destination and SHA-256 map for every
selected original artifact. `attestations/` contains the exact original manifests,
authenticated against the externally supplied frozen anchors. Those manifests
also list omitted files: their presence does not assert that the complete original
packet is included. The standalone verifier checks each selected original file's
membership in its own anchored manifest, then exact membership of this bundle.
`DEPENDENCIES.json` gives immutable OpenAI Math raw URLs at commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and original source hash receipts, plus
versioned primary-paper URLs and hashes. Original receipt path strings may name
private repository locations; no corresponding source bodies are included.
Lean dependency URLs and immutable revisions are in the selected lake manifest.

Active manuscript: t298p-manuscript-r2, manifest
`afc2c2ad6ecd45ef9958092c343e99b9d2804cb8f771a3d54cccae3e426393dc`.
The revision response records the bilinear/Hilbert-adjoint convention correction
and finite-real, standard-axiom, trusted-cache disclosures. The paper's historical
README describes its original manuscript packet, not this selected bundle.

Selected evidence includes the original r104 argument and scope freeze, completed
proof review r2, contribution review r2, attribution responses r1/r2, scoped formal
author r1 and independent formal review r2. Original prose with pending-review
language remains historical evidence. The contribution verdict is SUBSTANTIAL
conditional on correctness, with bounded search/novelty claims, not worldwide
priority or exhaustive literature clearance. The attribution responses are author
responses, not independent reviews.

The proof review's section 6 leading-score equality has a known exposition typo:
the correct equality is sum_j ||Xi_j^0||^2 = Phi*(U)/(epsilon^2*k^4). The preceding
score expression, original argument, Lean leading_score_energy and active paper
use the correct normalization. Preserve the review's original bytes and read it
with this explicit correction.

Original `verify.py`, repository input-audits, manuscript `controls.py` and their
private-source prerequisites are contextual checks. They are deliberately not
selected as portable verification commands: their source-body checks require the
full research repository and private source copies. They are NOT silently skipped
under a standalone PASS. Original source-reading and proof reviews remain cited
human evidence. Standalone verification means only bundle identity, selected
original membership, exact PDF reconstruction, fresh scoped Lean support/controls,
and independent supplement/sensitivity replay under the disclosed trust boundary.
The finite pairing and arithmetic scripts in the paper are diagnostics, not a
proof of the analytic theorem.

Final assembly additionally requires an actual sealed independent manuscript
review, its external manifest anchor, and a parent-vetted layout policy with its
own external anchor. No acceptance file is required or used. The policy identifies
the actual verdict, empty required-findings array, manuscript-manifest binding,
human review report and public selected review members; it is an authenticated
adapter, not an inferred schema. An external policy is a trust input: the parent
must verify that its pointers select the real gate fields. The tool never creates
a PASS or rewrites a review verdict. Preparation has no manuscript-review policy.
Even a final local reviewable package retains accepted=false, count_change=0,
published=false and full_theorem_formalized=false.
