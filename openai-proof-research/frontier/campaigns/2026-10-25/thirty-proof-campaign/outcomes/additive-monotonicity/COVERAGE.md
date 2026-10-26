# Exact coverage

- `KAdditive`: every ordered k-tuple drawn from E, with the actual sums.
- `count`: cardinality of the actual finite set of arithmetic functions filtered by KAdditive.
- `identity_additive`: all sets E and arities k.
- `exceptional_not_two`: explicit tuple (1,1) falsifies the predicate.
- `exceptional_three`: every admissible tuple equals (1,1,1), so the predicate holds universally.
- `identity_ne_exceptional`: values at 2 distinguish the two functions.
- `count_two`, `count_three`: exact cardinalities 1 and 2.
- `monotonicity_counterexample`: ordered arities and strict increase refute the literal count claim.

The source-attribution audit is documentary rather than a Lean theorem. The proof concerns the unrestricted statement in MathDB, interpreted as counting solutions to the displayed additive relation. A different meaning of “determined”, or added hypotheses on E or S, requires a different theorem and is not covered. No result about multiplicative arithmetic functions is claimed.
