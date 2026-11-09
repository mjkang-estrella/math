# Canonical coverage and generic reduction

Namespace `Polyomino57.Diagonal`, importing the byte-identical inherited `SignedNormalization` chain. Actual frozen Cartesian `GridPoint`, `EdgeConnected`, `translate`, `witness`, `UniversalContainer` are used.

* `Recoverable P Q`: `(∃ t, translate t Q ⊆ witness) → ∃ t, translate t P ⊆ witness`. `recoverable_trans`, `translate_recoverable`, `affine_recoverable` compose recovery using the frozen literal D4 invariance. Final placement permits only translation of original P.
* `swap_box`: reflection y↦−y followed by integral shift `inverse (-e) e` swaps a,b, preserving e, bounds and all four attained extrema.
* `odd_a_box`, `odd_b_box`: the inherited integral odd-span formulas transport every domain bound and all four attained extrema to parity zero. `affine_card` and `affine_connected` transport literal cardinality/connectivity.
* `parity_coverage`: sorted spans with e∈{0,1} produce a canonical box, preserving cardinality, connectivity, extrema and recovery.
* `canonical_coverage {P} (hc : EdgeConnected P) (hn : P.card = 11)`:
  `∃ a b e Q, Canonical a b e ∧ Q ⊆ domain a b e ∧ ExactExtrema Q a b e ∧ EdgeConnected Q ∧ Q.card = 11 ∧ Recoverable P Q`.
  No assumed bounding box, normalization, parity, tree representation or geometry premise.
* `mem_canonicalCases a b e`: `(a,b,e) ∈ canonicalCases ↔ Canonical a b e`. Combined with inherited `canonicalCases_card : canonicalCases.card = 70`, this connects coverage to the explicit finite set.
* `FiniteCases`: `∀ c ∈ canonicalCases, ∀ Q : Finset GridPoint, Q ⊆ domain c.1 c.2.1 c.2.2 → EdgeConnected Q → Q.card = 11 → ¬ HitsAll Q (groups c.1 c.2.1 c.2.2)`.
* `universalContainer_of_finiteCases (finiteCases : FiniteCases) : UniversalContainer 11 witness`.
  This includes the frozen proof of witness connectivity, because the actual definition is a conjunction. No extra coverage/recovery premise. The 70 finite-case assertions intentionally remain the only hypothesis. No finite-case assertion is proved here.

New mathematical module is safe, nonpartial, standard three axioms only. The inherited generated `Polyomino57.attachCheck._unsafe_rec` remains partial=true, unsafe=false, axiom=false; the audit permits precisely that inherited flag exception. All inherited formal sources, including the old audit, are byte-identical. New `CanonicalAudit` extends the audit to the new origin.
