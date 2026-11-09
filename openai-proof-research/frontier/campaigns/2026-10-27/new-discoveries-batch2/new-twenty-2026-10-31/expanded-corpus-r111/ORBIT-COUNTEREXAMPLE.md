# 373123: candidate refutation at n = 20, m = 6

Status: ordinary exact computation and two independent mathematical routes agree;
no literal Lean endpoint. Zero accepted credit. This is the highest-priority lead.

Hai Zhu, *Plethysm and orbit harmonics*, arXiv:2602.12623, Proposition 3.29,
Equation (1.4), and Conjecture 4.3 are the exact source. The source defines
G-log-concavity by G-module injections V_(d-1) ⊗ V_(d+1) → V_d ⊗ V_d,
over complex representations, with the diagonal tensor action. Proposition 3.29
identifies V_d = R(Π_(n,m))_d with the permutation representation on unordered
partitions of [n] into n-d blocks, each block of size at most m. It does not
establish the required tensor inequalities. The author's reported verification
is 9 ≤ n ≤ 16; the nearby n ≤ 20 statement concerns DIFFERENT modules in
Conjecture 4.2, not this target.

Take n = 20, m = 6, d = 15. Write P_k for the permutation representation on
partitions into k nonempty blocks, each of size at most six. The desired injection
is P_6 ⊗ P_4 → P_5 ⊗ P_5. The sign-representation multiplicities are respectively
4 and 1. Thus the sign isotypic part already obstructs this injection.

## First exact route: character calculation

`scripts/orbits.py` computes complete symmetric functions in the power-sum basis,
plethysms h_a[h_b] by the Newton recurrence, and Proposition 3.29's character for
each degree. It computes irreducible characters by the beta-number form of
Murnaghan–Nakayama, checks each character's exact orthogonality norm, and computes
Kronecker differences by conjugacy-class inner products. No floating point is used.
For n = 17 and 18, every tested m has nonnegative Schur differences. At n = 20,
every 6 ≤ m ≤ 20 gives coefficient -3 for s_(1^20) at degree 15. Every other
coefficient tested is nonnegative; this is not a minimality assertion.

## Independent route: pairs of set partitions

The tensor of two permutation representations is the permutation representation
on ordered pairs of partitions. Its orbits correspond to nonnegative contingency
matrices under independent row and column permutations. Matrix entries are the
intersection sizes of blocks; row and column sums are the block sizes.

On a transitive G-set G/H, the sign representation has multiplicity one if all
members of H are even, and zero otherwise. This follows directly by assigning
a sign-equivariant function its value on a single orbit representative; an odd
stabilizer forces that value to be zero. If any intersection has size at least two,
its internal transposition is an odd stabilizer. Therefore only binary matrices
can contribute. With twenty elements, P_5 × P_5 needs twenty ones in a 5 × 5
matrix, or five holes. P_4 × P_6 needs twenty ones in a 4 × 6 matrix, or four holes.
Every row and column sum is at most six automatically. Nonempty blocks require
no zero row or column.

`scripts/sign_orbits.py` enumerates these binary matrices exactly. It minimizes
column encodings over every row permutation and then sorts columns, a complete
canonicalization under both row and column permutations. There are 32 orbits in
the 5 × 5 case and 15 in the 4 × 6 case. To test stabilizer parity it enumerates
all row permutations compatible with the column multiset, chooses one matching
column permutation for each, and also tests generators swapping identical columns.
These generate the full stabilizer. It computes the induced permutation on the
TWENTY PRESENT EDGES; vertex-permutation parity alone would be incorrect.

The complete sign-supporting list, encoded by bit masks for HOLES in successive
columns (bit i means missing row i), is:

| Size | Hole masks | Sign multiplicity |
| --- | --- | --- |
| 5 × 5 | (0, 1, 1, 2, 12) | 1 |
| 4 × 6 | (0, 0, 0, 0, 3, 3) | 1 |
| 4 × 6 | (0, 0, 0, 1, 2, 3) | 1 |
| 4 × 6 | (0, 0, 0, 0, 3, 5) | 1 |
| 4 × 6 | (0, 0, 0, 1, 2, 5) | 1 |

Every other orbit has an odd stabilizer. Full representatives and rejection
witnesses are in `outputs/sign-orbits.json`. This independently gives 1 - 4 = -3,
matching the symmetric-function computation without using its code or character
table. All integers and permutations are exact.

## Missing formal endpoint

A literal Lean certificate must define Π_(20,6) as the source's actual finite
partition locus and its orbit-harmonics ring, establish the graded permutation
module bridge of Proposition 3.29, define the sign isotypic subspaces, and prove
that any injective equivariant linear map restricts injectively to those subspaces.
The pair-partition/contingency-matrix orbit equivalence, odd intersection stabilizer,
binary-matrix orbit completeness, and exact parity certificates must then be
kernel checked. One could instead formalize the Frobenius/character route, but
that has substantial symmetric-function infrastructure requirements. No such
bridges are silently assumed in a Lean theorem here. There is no Lean packet,
strict replay, or transitive axiom audit to report.

## Novelty and significance limits

The current Omega D5 and Problems path inventories and bounded public searches
were screened. No matching resolution was located, but this is not exhaustive
literature clearance or an independent significance decision. The original source
already reports failures at n = 7,8; this witness is inside its conjectured range
n ≥ 9 and beyond the verified range, so it is not an endpoint correction. The
negative coefficient requires a new exact calculation, rather than simply adding
the source's existing inequalities. Root must still judge eligibility and arrange
independent adversarial review. No author contact or publication occurred.
