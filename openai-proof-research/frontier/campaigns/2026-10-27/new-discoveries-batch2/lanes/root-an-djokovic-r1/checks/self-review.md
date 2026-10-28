# Worker self-review (not independent review)

The source sign and normalization were attacked in three independent finite calculations: sparse expansion of the literal source χ_J paired with the signed descending-staircase Vandermonde; direct Fraction-valued summation over distinct nodes for D_n(P); and first-deficit coefficient regrouping. All agree with the conjecture. They are tests, not the proof.

Mathematical points checked:

1. The non-path factors are exactly i<j−1, not i≤j−1. Adjacent factors are divided out of Δ, and the remaining n−1 factors have the same orientation as P in the source.
2. Alternation has n! summands, but its leading staircase coefficient is the coefficient inner product itself, not n! times it. Each distinct staircase permutation appears once. This is different from pairing Δ with itself, which is n!.
3. Every internal variable is present in exactly one numerator factor; endpoints may have large exponents. Thus decreasing defects holds precisely on j=1,…,n−1, where it is used. No constraint on the final n-th increment is needed.
4. Signed coefficients can cancel. C_j sums signed coefficient mass, not a positive count. The zero-specialization argument annihilates each degree sum and is therefore valid with cancellations.
5. For j<k the vanishing factor is x_n−x_(j+1), which exists because j+1≤k<n. For j>k it is x_(k+1)−x_1, which exists because k+1≤j<n. At j=k all factors are 1−t, not a mix of t−1 and 1−t.
6. C_0=0 because P(1,…,1)=0 with n−1≥1; C_n=0 because no first-negative index exceeds n. The endpoints k=1 and k=n−1 remain inside g_1,…,g_n. n=2,k=1 yields −2 as required.
7. The self-contained transfer proof never moves a negative exponent. Before the omitted position, process from the left with every prefix at least its length. After it, process from the right with every suffix at least its length. The total mass on each side prevents a transfer into the omitted position. Every move lies in a zero case of the proved edge-splitting identity.
8. The canonical-monomial recurrence has sign (-1)^(n-r), and the unique additive constant is fixed by D_n(e_(n-1))=0 over Q, where division by n is valid. The induction includes the one-variable block D_1(1)=1.
9. A simple reason the source's Theorem6.2 is not already a direct all-parameter answer: its values are signed products of distinct members of {2,…,n}, hence divide n!. At n=8,k=4 the known conjectured value is 1400=2^3*5^2*7, which does not divide 8!. This rules out merely relabelling that source family to get every J_(k,n). It does NOT rule out a classical divided-symmetrization subsumption.

Strongest remaining objections: no independent reviewer; bounded source search only; arXiv-to-final-journal comparison incomplete; campaign may reject the additional two-level cancellation as routine; Lean lacks the literal endpoint. No accepted credit warranted yet.
