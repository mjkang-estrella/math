# 354228: statement-correspondence plan (draft; nothing compiled in this lane)

| Source / MathDB notion | Lean draft object | Notes |
|---|---|---|
| complete full t-ary tree with n levels (every nonleaf has t children; all leaves have the same depth) | `tree t n` on `TVert t n` = words over `Fin t` of length ≤ n; `u ~ v` iff one is the other plus one letter | Rooted at `[]`. All leaves have depth n by construction. For the "every such tree" quantifier, note that every complete full t-ary tree is isomorphic to `tree t n` for its depth n; this needs one isomorphism lemma (or state the theorem for the canonical model and note isomorphism invariance of χ_la). |
| local antimagic labeling: a bijection E → {1,…,\|E\|} with w(u) ≠ w(v) on edges | `IsLocalAntimagic G f` with `f : G.edgeSet ≃ Fin \|E\|` and the label `f e + 1` | The shift by 1 is explicit in `wsum`. |
| χ_la = the minimum number of colours of induced colourings | `chiLA` = `sInf` of `card (image (wsum f))` over local antimagic f | Nonemptiness comes from `upper_bound`. |
| l = number of leaves (degree-one vertices) | `numLeaves` = number of vertices of degree 1 | For n ≥ 1 and t ≥ 2 this equals t^n (lemma L7). |
| "for every even t ≥ 2" | hypotheses `2 ≤ t`, `Even t` | We also assume n ≥ 1; the depth-0 tree K_1 has no edges and is outside the source's scope. |

Recommended engineering: define the labeling arithmetically on (row h, position p) by explicit case formulas, and prove L1 (bijectivity) by showing that the levels map onto the sets A_1, A_h (shells) and the tuple blocks. The `decide` route is not viable for the general theorem. Estimated size: several thousand lines (heavy). A cheaper, partial and NOT literal milestone would be a kernel `decide` check of fixed small instances (t, n) ∈ {(2,3), (4,2), (4,3)} via a checked labeling list. Such instances do not prove the conjecture.
