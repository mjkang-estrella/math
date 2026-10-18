# Manuscript response to the frozen reviews

This is author manuscript preparation, not an independent review or acceptance decision. The full original T205M quantifiers are unchanged. Frozen source, author, review and formal packets were not edited.

## Contribution corrections

- C1: Sections 1 and 2, the first definition of R, Section 8 and bibliography entry I19 explicitly credit I19 §4 for the band multiplicity recursion and the rule of maximizing separate quotient bounds. I21 §2.1 supplies the inherited dominance/Kostka refinement. The residual estimate is the four-exception uniform induction, not the recursion itself.
- C2: Abstract, introduction and conclusion distinguish new-to-project from unproved new-to-literature priority. The entire high-capacity proof is included and credited to parent author assistance. No parent assistance is described as independent review.

## Full proof review E1–E6

- E1: Section 5.1 replaces reliance on Kirillov's ambiguous matrix-width wording with an actual reading of Kirillov–Schilling–Shimozono, arXiv math/9901037v1, §2.2 equations (2.4)–(2.6), Theorem 2.10, together with the §2.1 representation multiplicity interpretation. Choose their target αᵗ and column rectangles R_a=(1^{μ_a}). Then ξ^(1)=μ, all other ξ vanish, the configuration sizes are the tails of α, and the vacancy formula is exactly the manuscript formula after folding ξ^(1) into ν^(0)=μ. The coefficient of s_{αᵗ} in ∏e_{μ_a} is K_{α,μ}, by ω and Young's rule. Partitions and vacancy lengths are unrestricted positive integers. This is a primary theorem application, not a finite diagnostic or conjectural correction of a misprint. Actual reading limits are in reading-limits.md.
- E2: Section 6 explicitly excludes L_1=h+1 by the area contradiction and separately excludes L_1=h. Only then is the low-capacity lemma applied at h.
- E3: Section 5 states the full first-vacancy formula, says equality with D_j holds for j≤t and also everywhere when s=0, and explains why the final maximal-weight factor remains one when the actual multiplicity differs at t.
- E4: Lemma 6.1 proves the critical-family LR identity for m≥5. Section 7 and the public README explicitly disclose that the finite verifier's last branch invokes this proved identity rather than independently computes it. The frozen proof review's separate LR recomputation at m=7,8 is credited as such, not claimed as our execution.
- E5: Proposition 2.1(iii) uses only four-row support of U_{m,2}. The stronger band identification is labelled inherited optional context.
- E6: The article has no campaign tally or acceptance assertion. Historical input documents are copied unchanged and may retain the status current at their creation.

## Scoped formal review E1–E7

The full new formal review was read. Section 7.3 now says 17 named declarations = 2 definitions + 15 theorems, with compiler-generated constants additionally audited by the reviewer. Coverage is generic finite-poset rank interpolation, the unique-rank ordered-cut implication and the two-ideal reduction. The geometric no-cut condition is explicitly unformalized, along with all representation theory and full induction.

E1 (auxiliary constants) is reflected in that wording. E2–E5 concern optional controls, regex inventory, optional git locking and a cosmetic lockfile project name; no immutable formal file is altered, and no claim is made that those changes were implemented. E6: the independent reviewer measured cache stability; the builder's `network_used` and `dependency_cache_modified` booleans are assertions, not such measurements. E7: fresh builder output goes to its requested output directory; `validation/` in the frozen packet contains copied development records. We do not claim to have rerun Lean or rebuilt the dependency object cache during manuscript preparation. The review remains relative to the pinned trusted Lean/cache objects.
