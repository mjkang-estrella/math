# Inspectable formal interface

All new generic definitions and theorems live in namespace GraphPotential.

- `Connected E T` means T.Nonempty and, for all x,y in T, `ReflTransGen (fun a b => a ∈ T ∧ b ∈ T ∧ E a b) x y`.
- `Hits H A T` means `∀ i ∈ A, ∃ v ∈ T, H i v`.
- `Certificate E D M H L` has exactly three fields. `L : Finset I → V → ℕ`, `H : I → V → Prop`. Both V and I have decidable equality.
- `base`: for nonempty A ⊆ M and z ∈ D, if `∀ i ∈ A, H i z`, then `L A z ≤ 1`.
- `edge`: for nonempty A ⊆ M and z,w ∈ D with E z w, `L A z ≤ L A w + 1`.
- `merge`: for disjoint nonempty A,B ⊆ M and z ∈ D, `L (A ∪ B) z + 1 ≤ L A z + L B z`.

The main theorem `soundness` takes a Certificate, Connected E T, T ⊆ D, z ∈ T, M.Nonempty, and Hits H M T. It concludes `L M z ≤ T.card`. It has no tree, decomposition, positivity, or empty-mask assumption.

The main grid wrapper `Polyomino57.potential_soundness` takes `GraphPotential.Certificate Polyomino57.Adj D M H L`, `Polyomino57.EdgeConnected P`, `P ⊆ D`, `z ∈ P`, `M.Nonempty`, and `GraphPotential.Hits H M P`. It concludes `L M z ≤ P.card`. The wrapper `potential_excludes_eleven` replaces a specified root with the condition `∀ z ∈ D, 12 ≤ L M z`, concluding `¬ P.card ≤ 11`.

Import Bridge to use both the generic and grid endpoints. Grid is the immutable byte-identical frozen module. The module path is relative to the extracted formal directory or the fresh-build directory created by replay.py. No certificates or table-entry proofs are embedded in this component.
