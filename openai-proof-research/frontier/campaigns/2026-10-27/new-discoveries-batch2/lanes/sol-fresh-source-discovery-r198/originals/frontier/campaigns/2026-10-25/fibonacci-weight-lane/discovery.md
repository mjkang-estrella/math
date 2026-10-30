# MathDB 371201: weight preservation for Fibonacci recurrences

Status: full theorem implemented; final clean rebuild and axiom audit recorded in `formal/build/audit.json`. No unpaid orbit/fiber bridge. This is a formal verification of an existing argument, with no novelty claim.

## Exact source and attribution

Marc T. Pudelko, *Modular Periodicity of Random Initialized Recurrences*, arXiv:2510.24882v2, 3 November 2025, Conjecture 17 and equation (19): <https://arxiv.org/html/2510.24882v2#Thmconjecture17>. The source's introduction identifies periods under cyclic equivalence, and Example 18 includes the zero fixed point with length one. The downloaded HTML and text are in `sources/`.

The counting proof is already posted by **Shivam Patel** on MathDB 371201, solution `b64f2547-2755-408d-8ca3-997917a47b33`, dated 20 August 2026. The assigned saved JSON and the extracted proof are preserved locally. This implementation verifies that argument; it does not claim a new proof or priority. The source metadata's 2026 description is not used to date arXiv v2: the source itself says 3 November 2025.

## Statement and quantifiers

For every pair of natural numbers `m,d` with `m ≠ 0`, `d ≠ 0`, and `d ∣ m`, every integer `eps`, and every cycle quotient class `q` of

`T_d(a,b) = (b,a + eps*b)` on `(ZMod d)²`,

sum `length(p)/m²` over **all** cycle quotient classes `p` of `T_m` whose reduction is `q`. The result equals `length(q)/d²`. Here length is the number of states in the quotient class; `orbitSize_eq_minimalPeriod` proves it equals the least positive return time. The main Lean theorem is `FibonacciWeight.fibonacci_weight_preservation`.

Taking `eps = 1` and `eps = -1` gives exactly the two recurrences in the source. The theorem also covers noncomposite positive moduli, `d=1`, `d=m`, and all integer coefficients. Removing the source's composite restriction strengthens rather than weakens its assertion. No coprimality condition on `eps` is needed because the explicit inverse always exists.

## Proof and formal bridge

1. `recurrence` is the actual permutation; its inverse is `(a,b) ↦ (b-eps*a,a)`.
2. `reduction` uses `ZMod.castHom` on both coordinates, is an additive homomorphism, is surjective, and commutes with the two actual recurrence permutations.
3. `Period T` is the quotient by `Equiv.Perm.SameCycle.setoid T`, including fixed points. `periodMap` is a well-defined quotient map, proved using commuting powers. `period_eq_iff_iterate` identifies its classes with time shifts.
4. `orbit_maps_onto` proves that the image of each upstairs orbit is the full indicated downstairs orbit.
5. `orbit_sum_eq_preimage` uses the quotient projection to partition the actual preimage into all upstairs classes. Its sum runs over actual orbit classes, not assumed numeric lengths.
6. `uniform_fibers` proves equality of fibers of a surjective additive homomorphism. `preimage_card` counts every selected preimage; `total_card` supplies the normalization. `reduction_fiber_card` specializes this to `(m/d)²`.
7. `weight_preservation` combines the preceding proved bridges, and `fibonacci_weight_preservation` instantiates it with the actual `ZMod` recurrence and reduction.

`zero_period_length` independently checks the delicate fixed-point convention: the zero orbit has length one.

## Validation and scope

The pinned Lean compiler is 4.34.1; mathlib revision is `d13f23b723b8a846827a245b89c10fc7d3f11612`. `formal/rebuild.py` validates all dependency revisions and tracked cleanliness, clears local compiled artifacts, rebuilds the source and Checks with warnings as errors, verifies complete declaration coverage, and enforces the allowed axioms `propext`, `Classical.choice`, `Quot.sound`.

`notes/review.md` is implementation self-review, not an independent reviewer endorsement. `paper/main.tex` contains the full mathematical proof and source attribution. No publication, shared-index change, or commit was made. The matrix extension mentioned in Patel's post is not claimed as a separately formalized theorem here.
