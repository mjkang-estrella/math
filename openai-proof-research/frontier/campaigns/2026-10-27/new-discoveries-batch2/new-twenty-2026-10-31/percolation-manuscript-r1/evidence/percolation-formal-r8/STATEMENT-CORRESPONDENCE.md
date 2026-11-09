# Statement correspondence

MathDB 333709 concerns Conjecture 20 of Gerbner–Keszegh–Meszaros–Patkos–Vizer, arXiv:1608.00531v1, SIAM J. Discrete Math. 32(2) (2018), 864–881. The inherited Lean proposition is:

`∀ (q : Nat) (P : Plane q) (r : Nat), 4 ≤ r → r ≤ q → ∃ a, Minimal P r a ∧ TimeIs P r a 2`.

The unchanged geometric endpoint refutes this universal proposition by the projective plane PG5 and threshold 5. NoMinimalTwoRound5 is the negation of the existence of a minimal infection on PG5 taking exactly two rounds. The normalization bridge maps any such witness to a valuation satisfying every generated normalized clause.

Numeric literal x corresponds to (abs(x)-1, x<0), which holds when the valuation differs from the sign Boolean. decodeVar maps numeric indices to structured SatVar values. Every named mask entailment quantifies over structured valuations satisfying normalizedCNF5. The input correspondence and normalization proofs are inherited byte-identically; this lane does not re-audit upstream truth or claim novelty.

Delivered endpoint: `Percolation.not_conjecture20_unconditional : ¬ Percolation.Conjecture20`.

Unconditional: the empty clause, normalized unsatisfiability and NoMinimalTwoRound5 are proved.
