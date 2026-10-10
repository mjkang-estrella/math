# First-pass research outcome — 2026-10-08

**Historical status:** the user subsequently requested continued discovery. See [active iterations](iterations/README.md); completion statements below refer only to this first pass.

**The requested significant, genuinely novel theorem was not achieved.** This pass produced checked technical results, rejected several overclaims, and identified exact missing steps. It did not prove a previously unresolved high-importance MathDB conjecture or establish a substantial new case of one. No candidate is being presented as a breakthrough.

## Scope and assumptions

The work used the actual theorem statements in OpenAI/math at revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` as true, as requested. Their proofs were not audited. Three broader geometry files at that revision are withdrawal notices rather than theorem manuscripts; historical withdrawn claims were not substituted for current premises.

MathDB's numerical significance scores concern news developments. Its problem importance bands are separate evidence. Hodge is a landmark target, Frankl is celebrated, and hot spots is named. No score was invented for this project's work. Nothing was submitted to MathDB or published externally.

## What survived deep review

| Record | Result | Separate finding commit | Limit |
|---|---|---|---|
| [R001](findings/R001-divisor-parallelogram-bound.md) | A restricted normalized divisor-walk family has negligible total absolute weight. | `ed50d45` | Does not control the longer traces and centering needed for the proposed Chowla route. |
| [R002](findings/R002-unweighted-kernel-obstruction.md) | Rare large entries invalidate the proposed norm bound for the specified undeleted, unweighted kernel. | `609a94c` | Rules out that implementation, not every weighted/deleted alternative. |
| [R003](findings/R003-polygon-eigenline-selection.md) | Polygonal corner analysis permits prescribed first-eigenline selection; the accepted smooth theorem then gives strict polygonal hot spots. | `b5103d9` | A modest extension of a known smooth mechanism, with literature priority unconfirmed; not the requested significant novel advance. |

These are project-level technical findings. The ten first-pass F001–F010 deductions remain archived and do not count toward the user's clarified objective.

## Why the main candidates were rejected or stopped

- **Frankl:** the noise and coding approaches supplied no improved general frequency bound. Parent review corrected a falsely claimed general falsification and an endpoint-supremum condition that was vacuous. Finite enumeration was reproduced, but was not treated as proof of an infinite-family claim.
- **K3/Hodge:** the arithmetic calculation compares two sufficient quadratic embedding hypotheses. It does not describe all known Hodge cases; the independent review gives an explicit CM counterexample to that overstatement. The proposed similitude lemma is Varesco's published Theorem 5.3. Transport from one arbitrary surface to an entire period locus was not justified. See the [K3 audit](reviews/geometry-k3-review-r2.md).
- **Mumford all-powers reduction:** after repairing degrees, twists, correspondence composition and the all-arity proof, the reduction is valid. An exact public predecessor was found in the October 2 H8 source. It constructs no exceptional cycle. See the [Mumford audit](reviews/geometry-mumford-review-r2.md).
- **Mumford sixfold partner:** the final audit accepts a repaired construction of a balanced split sixfold B with a level-one piece U of H³(B) satisfying U(1) ≅ H¹(A) ⊗ K. The accepted split-sixfold theorem supplies HC on powers of B. Transferring it back requires an algebraic class in the H¹(A) ⊗ H³(B) component of A×B. That class was not constructed. The construction is classical in substance; the exact determinant specialization has unverified priority. See the [final partner audit](reviews/geometry-partner-review-r3.md).

The most concrete remaining hypothesis from this pass is therefore: **construct a codimension-two cycle on A×B with nonzero H¹(A)⊗H³(B) component for an actual Mumford fourfold A and its reviewed partner B.** The final audit proves that this would imply HC on all powers of that A. Restating this conditional reduction is not itself progress on its algebraicity hypothesis.

The alternative rank-13 K3/KS reduction also has explicit prior art. Neither CM density nor the finite tangent-rank calculations manufacture a deformable cycle. Semiregularity would require an actual object and control of its full obstruction theory. Those remain missing, not ruled out in principle.

## Validation record

Independent T3 agents checked proofs and searched primary literature; the parent read the audits, checked source contracts, reproduced the relevant exact-arithmetic outputs, and committed corrections. The final geometry audit verified nine source downloads plus 37 immutable prior-art source files, and its independent central-character and tangent-rank output reproduced exactly. Earlier checks include 1,000 independent K3 arithmetic tests, symbolic Mumford tensor-generation identities, and independent polygon corner/stress tests.

Finite computations verify finite algebra only. Universal conclusions depend on the written proofs and explicitly accepted premises. None of this constitutes external peer review, a publication-priority guarantee, or proof-assistant certification. All delegated tasks in this pass have returned; no background research task is left running.
