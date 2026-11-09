# Checked work and exact remaining interfaces

The literal sum is over `range (K+1)` and `univ.powerset` for Fin 4, with sign `(-1 : Int)^(4-T.card)` and the cast of the NATURAL quotient. This distinction was corrected during development; final types and audit logs expose it literally. Repeated values remain indexed separately.

The single-subset formula is proved by a pointwise division decomposition below 5m and an induction on H counting `r ≤ j+s`. That induction proves both threshold boundaries with no generic-position premise. Summation commutation and multiplication distribution yield the exact 64-clamp sum. Bounds hold also for m=1 and H=m; neither value is excluded by a strict inequality. The source bridge is proved for real floor and rational floor, with the positive-denominator/nonnegative-argument facts explicit.

Permutation is a finite-set equivalence induced by a permutation of Fin 4; it preserves cardinality and subset sums. Tuple.sort supplies the monotone representative even with ties. Integer division by 3 is connected to `3*t ≤ m ≤ 3*t+2` by a universally quantified omega proof.

Remaining central interface, verbatim in mathematical notation:
`∀ m H : Nat, 0<m → 1≤H → H≤m → ∀ a : Fin 4 → Nat, (∀ i, a i<m) → Monotone a → -3*Int.ofNat(m/3) ≤ clampedSum m H a`.

To complete the intended endpoint, prove this proposition unconditionally. The reviewed DAG could supply it only after actual typed elaboration of every reachable proof node, exact query correspondence, conservative ite definitions and residual-hypothesis discharge. Universal Lean arithmetic leaves and propositional proof terms would avoid trusting Python. None of that work is silently represented by the conditional transfer theorem. No claim that an imported checker solves this interface is made.

The source-side reduction and sorting are complete checked components. The full endpoint is not complete. This lane does not clear prior art or acceptance, and does not count the reduction as a discovery.
