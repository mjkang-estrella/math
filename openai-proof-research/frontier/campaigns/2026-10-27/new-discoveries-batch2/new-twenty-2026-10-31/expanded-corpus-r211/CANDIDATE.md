# No qualifying candidate

This lane proposes no new result for acceptance and no Lean endpoint. All twenty records have zero discovery credit. The most concrete obstruction found is explicitly ineligible under the task's small-modification rule.

## 334721: uncredited one-vertex modification

Source: Brown and Erey, *Restraints Permitting the Largest Number of Colourings*, arXiv:1611.09536v1, Definition 2.4 and Conjecture 5.1. A simple restraint assigns a forbidden colour to each vertex. The objective maximizes the number of permitted proper x-colourings for all sufficiently large x, and equivalence permits cycle automorphisms and a global colour relabelling.

For C11, with zero-based colour names, the source restraint is

`[0,1,0,1,0,2,1,2,1,2,1]`.

Its canonical representative under those equivalences is

`[0,1,0,1,0,1,2,0,2,0,2]`.

Changing only its eighth entry gives the competing canonical restraint

`[0,1,0,1,0,1,2,1,2,0,2]`.

The exact difference (competitor minus source) is

`x^7 - 15*x^6 + 102*x^5 - 405*x^4 + 1012*x^3 - 1592*x^2 + 1464*x - 611`.

Its leading coefficient is positive, so the competitor eventually permits strictly more proper colourings. This is a diagnostic ordinary refutation of the source's displayed formula, independent of its ambiguous progression endpoints when n is 1 modulo 4: here n=11 is 3 modulo 4 and all displayed ranges have literal endpoints. It is not a qualifying discovery: a single forbidden-colour change of a printed construction is expressly excluded. No claim of global novelty, independent review, or root acceptance is made.

The polynomial calculation uses edge inclusion-exclusion. For A a subset of cycle edges, let its spanning components be B. Equality along edges of A forces each B to receive one colour, leaving exactly x minus the number of distinct forbidden colours in B possibilities. Thus the restrained polynomial is

`sum_A (-1)^|A| product_B (x - |{r(v) : v in B}|)`.

The search considers the restraints with exactly three constant runs in the step-two cyclic order. It exhausts all positive run-length compositions within that family for odd n from 5 to 17 and quotients by dihedral and colour symmetries. It is not advertised as an independently proved exhaustive search of all restraints; the reduction to maximal distance-two repetitions uses source coefficient conditions and would need a semantic proof for a full theorem. No such reduction is necessary for the fixed two-polynomial comparison.

Scripts: `scripts/restraints.py`, `scripts/restraint-compare.py`, and `scripts/restraint_independent.py`. Exact polynomial arrays and independent colour-transfer checks are retained in `outputs/`. These are ordinary computations, not kernel certificates.

## Other sustained routes and precise gaps

- **329897, Building Nim.** Exact memoized minimax uses sorted stack heights and Bouton's terminal XOR criterion. Odd-stack scope follows the actual source; the even-stack counterexamples are already explicit there. The source verified through 34 tokens for odd stack counts from 5 through 19. This lane extends selected stack counts substantially, with completed ranges in `outputs/nim-*.json`. There is no uniform strategy or Lean proof.
- **330128, competition graphs.** Every permutation through length 10 was enumerated. Competition adjacency is computed from the existence of an earlier point smaller than both predators. Isomorphism matching against graphs from 123-avoiding permutations found no counterexample. A proof must preserve the exact vertex budget, including isolated prey/witness vertices. A general claw-free interval-graph representation alone leaves that bridge unresolved.
- **322962, core increments.** Exact generating-product coefficients check all n from 63 through 700 and every required t from 4 through n-7. No violation. Need a uniform inequality in both parameters; this bounded q-series computation proves no infinite statement.
- **328340, divisibility graphs.** All integer partitions through degree 30 yield exact symmetric/alternating conjugacy-class sizes, with splitting of distinct odd cycle types handled. All-pairs component distances give diameter at most four. No proof covers arbitrary degree.

The task requires substantial new mathematics, not merely a short certificate. The excluded odd-cycle calculation must not be promoted to a candidate by adding a Lean proof.
