# Proof and finite certificate

`Definitions.lean` gives the literal definitions for all natural n.
`Bridge.lean` builds the exponent vector `degreeSet R E`. Its values at the x
and y variables are the respective set indicators, so it is injective in the
pair of sets. `term_eq_monomial` and `coeff_rawSum` identify the target
coefficient with the sum of literal inversion signs over permutations having
exactly those sets and satisfying the partition condition.

For n = 9 the target sets are R = {0,4,6,7}, E = {1,2,3,5,8} in zero-based
notation. `Finite.lean` proves that inverse positions of values 1,2,3 are
0,1,2. It also proves that value 7 occupies the last position: the last value
is an RLM, and RLM values increase with their positions.

Five inverse positions remain, for values 0,4,5,6,8. Each lies between 3 and
7 and all are distinct. The RLM conditions imply pos(0) < pos(4) < pos(6).
The excedance set implies pos(4) ≥ 4, pos(6) ≥ 6, and pos(5) ≤ 4.
`Arithmetic.lean` classifies these five integers by bounded interval cases.
It enumerates at most five choices at each of five positions, with arithmetic
pruning; it never enumerates all 9! permutations. Exactly eight possibilities
remain. `Characterization.lean` converts each to equality of inverse maps,
hence permutations, and proves the converse by concrete set checks.

`Concrete.lean` defines all eight permutations with explicit forward and
inverse tables, whose inverse identities are proved by kernel `decide`.
It checks their sets, inversion counts, complete partitions and the cycle
conditions by kernel reduction. In the order p0 through p7 their one-based
words, inversion counts and partitions are:

| Name | Word | inv | Partition | All parts ≥ 3 |
| --- | --- | --- | --- | --- |
| p0 | 2 3 4 6 1 5 9 7 8 | 7 | 6,3 | yes |
| p1 | 2 3 4 6 1 9 5 7 8 | 8 | 9 | yes |
| p2 | 2 3 4 6 9 1 5 7 8 | 9 | 5,4 | yes |
| p3 | 2 3 4 1 6 5 9 7 8 | 6 | 4,3,2 | no |
| p4 | 2 3 4 1 6 9 5 7 8 | 7 | 5,4 | yes |
| p5 | 2 3 4 9 6 1 5 7 8 | 10 | 9 | yes |
| p6 | 2 3 4 1 6 5 7 9 8 | 5 | 4,2,2,1 | no |
| p7 | 2 3 4 6 1 5 7 9 8 | 6 | 6,2,1 | no |

`Endpoint.lean` reduces the contributing set to {p0,p1,p2,p4,p5} and sums
−1 + 1 −1 −1 + 1 = −1. Literal map membership would make this coefficient
a natural-number cast, hence nonnegative, giving both contradictions.

`Control.lean` proves `InNat (F 3 3)`. It checks that every admissible S_3
permutation has positive literal inversion sign, then constructs the natural
polynomial explicitly as the sum of natural monomials. This is a meaningful
valid instance in the source's domain, rather than only a failed positivity
check. S_3 enumeration has only six elements.

This certificate establishes only the (9,3) witness and the dual negation.
The candidate's infinite family and the optional (8,3) witness are not formalized.
