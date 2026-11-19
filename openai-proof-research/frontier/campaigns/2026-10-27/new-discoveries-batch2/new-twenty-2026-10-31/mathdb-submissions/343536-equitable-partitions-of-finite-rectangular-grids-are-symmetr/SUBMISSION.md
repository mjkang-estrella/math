# MathDB 343536: Equitable partitions of finite rectangular grids are symmetry orbits (Neuberger-Sieben-Swift Conjecture 5.6)

- Problem: https://mathdb.com/p/343536
- Source: Neuberger-Sieben-Swift arXiv:1908.05797 Conjecture 5.6; MathDB 343536
- Outcome: **PROVED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `GridFinal6.mathdb_343536 : ∀ m n ≥ 1, (∀ r : Setoid (Fin m × Fin n), IsEquitable (G m n) r ↔ ∃ H : Subgroup (G m n ≃g G m n), r = orbitSetoid (G m n) H) ∧ (Nonempty (EqPart (G m n) ≃o Subgroup (G m n ≃g G m n)) ↔ HasFreeVertex (G m n)) ∧ (HasFreeVertex (G m n) ↔ ¬ (2 ≤ m ∧ m = n ∧ n ≤ 3)), with G m n the Mathlib box product of paths`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `paper.pdf`
- Lean source: `grid-formal-r6-source.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: SIADS, Brito-Manoel and Godsil bodies not read; Godsil compact-graph channel not exhaustively excluded; bounded citing-work search only trust_limits: Prebuilt upstream Mathlib oleans trusted, except Mathlib.Tactic.Bound.Attribute, recompiled locally from pinned read-only source by the packet driver; leanchecker shares the installation; round-6 development audit briefly overlapped the lane's fresh replay (terminated, excluded); root replay serial; root replay attempt 1 failed only on missing executable bits (recorded) not_claimed: Priority for the path case; Results for infinite or periodic grids; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Proved: the Neuberger-Sieben-Swift conjecture for rectangular grids, for all m, n >= 1. Every equitable partition of the grid graph P_m by P_n is the orbit partition of a subgroup of its automorphism group; the equitable-partition lattice is isomorphic to the subgroup lattice exactly when a free vertex exists; and a free vertex exists unless 2 <= m = n <= 3. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Neuberger, Sieben and Swift, arXiv:1908.05797 (SIAM J. Appl. Dyn. Syst. 19 (2020)), Conjecture 5.6, proved for all m, n >= 1: every equitable partition of P_m □ P_n is the orbit partition of a subgroup of the automorphism group; the equitable-partition lattice is isomorphic to the subgroup lattice exactly when a free vertex exists; and a free vertex exists unless 2 <= m = n <= 3.

## Body (paste into the MathDB body field)

Use the written proof in this folder: paper.pdf. The complete Lean source is in grid-formal-r6-source.zip.
