# Statement correspondence for MathDB 381433

The survey is the hash-bound `inputs/adverse-formal-r1/inputs/sources/381433.txt`, arXiv:1811.05516. The original PDF and inherited receipts are preserved in `inputs/`. No new prior-art search was made. The inherited root ruling is `QUALIFIED_PROCEED`, not novelty clearance.

| Source requirement | Literal Lean declaration / proof |
| --- | --- |
| Finite simple graph with at least one edge | `latinGraph : SimpleGraph (ZMod 6 × ZMod 6)`; edge `(0,0),(0,1)` in `refutation_of_source_statement` |
| Distinct cells sharing row, column, or cyclic symbol | `latinGraph` in Definitions.lean |
| Real adjacency matrix | `adjacency` with entries 1 or 0 |
| Least real adjacency eigenvalue | `realEigenvalues`, `leastEigenvalue := sInf realEigenvalues`; `gram_eigenvalue_lower`, `leastEigenvalue_eq_of_gram`, `global_least`, `deletion_least`. The last two proofs exhibit nonzero eigenvectors at −3, so the infima are attained. |
| Equation (11), H = A / (−λmin), x ≥ 0 | `objective`, `upsilon := sSup {r | ∃ x ≥ 0, r = objective G x}`. `objective_gram`, `objective_le_six`, `upsilon_eq_six` prove the bound, feasibility, attainment, and supremum equality. |
| Stability number α | `Independent`, `alpha := sSup` of independent finset cardinalities; `alpha_eq_five` proves the maximum is 5, attained by `independentFive`. |
| G − N(v), deleting the open neighbourhood | `deletionVertices G v := {w // ¬G.Adj v w}` and `deleteOpen := G.induce ...`; the base vertex is retained. |
| A = BᵀB − 3I | `incidence_identityQ`, its real lift `incidence_identityR`, and restriction `deletion_gram`. |
| Kernel and nonnegative fractional certificates for every v | `certificate_i_j` for all 36 pairs; `all_certificates`; `deletion_kernel_sum`, `deletion_fractional_sum`. Exact rational coordinates are copied from the inherited certificate. |
| No isolated vertices in G | `no_isolated_vertices`. No such condition is imposed on deletion graphs. |
| Both invariants integral and unchanged by every deletion | `Adverse`; `graph_adverse`, using `global_least = -3`, `global_upsilon = 6`, `deletion_least`, `deletion_upsilon`. |
| Q means α = υ | `QGraph`; `graph_not_Q`, using 5 ≠ 6. |
| Conjecture 4.2, all adverse graphs are Q | `SourceConjecture` universally quantifies over all `Type` vertex types with `Fintype`, requiring an edge; `refutation_of_source_statement : ¬SourceConjecture`. `refutation` also negates the version without the ambient edge restriction. |

The source's formula governs the normalization. The survey's sentence calling H itself positive semidefinite is not used; H + I is the matrix in (11). The formal supremum equals an attained maximum for the witness and for every deletion. Definitions on unrelated edge-free graphs do not affect the source theorem because `SourceConjecture` has the edge hypothesis.

There are no assumed numerical invariants, certificate axioms, omitted real-matrix bridges, finite-only surrogates for the universal conjecture, or hypotheses assuming adversity. `graph_adverse` is proved. Kernel-reduced `decide +kernel` is used for sound finite rational checks; no native evaluation proof oracle is used.

## Dossier additions

Reviewer.lean is reviewer-authored, copied byte-identically from
adverse-review-r1/extracted/formal/Reviewer.lean. Its definitions
IndependentReview.NonComplete and IndependentReview.SourceRestatement spell
out a distinct nonedge, an edge, no isolated vertices, both integral invariants,
all open-deletion equalities and the Q equality. Its noncomplete theorem uses
(0,0),(1,1), and IndependentReview.refutes_stricter_source negates that stricter
universal assertion. DossierAudit enumerates all 167 declarations in the 13
original proof modules plus Reviewer, including generated declarations; it
checks complete transitive axiom sets and emits full types and bodies.
The original Audit.lean remains byte-identical too.

The inherited correspondence's historical root-ruling sentence describes its
own earlier state. The dossier also preserves adverse-root-adjudication-r2.json:
QUALIFIED_PASS for manuscript and root final replay, zero accepted credit,
Luz 2020 unread, no priority claim. This draft performs no new literature search.
