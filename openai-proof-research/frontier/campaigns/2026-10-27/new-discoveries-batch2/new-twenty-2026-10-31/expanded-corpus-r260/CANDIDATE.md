# 324209: conditional finite certificate route, not a discovered counterexample

Zero credit. No witness, full ordinary endpoint, Lean proof or execution result is claimed. Root must close the remaining literature and current registry gates before routing investment to Pi. The precise next diagnostic below is executable; it is not an assertion that a feasible matrix exists.

The literal target is Swanepoel's unbalanced extremal quantity C(k,d), called overlined C in v1, not the strongly balanced CB(k,d). Source: arXiv:1210.0366v1 Conjecture 26; v2 Conjecture 29. The final accepted author manuscript is cached. The purported AMS PDF request returned HTTP 200 HTML, not a paper, so the publisher body remains unread. This distinction is recorded rather than treating 200 as clearance.

## Source-faithful finite target

Try d=14, k=26, m=29. The parameter inequality holds since 2d-sqrt(d/2)=28-sqrt(7)<26. A rational 29 by 29 matrix A with diagonal 1, all entries in [-1,1], rank at most 14, and every 26-entry sum in every row in [-1,1] would refute the literal assertion.

This is an exact bridge, not numerical evidence: use the columns x_j of A in their real linear span with the inherited infinity norm. Diagonal 1 and entry bounds give norm exactly 1 for each column. Row subset bounds give the collapsing condition. Factorization A=UV, with U of size 29 by 14 and V of size 14 by 29, bounds the dimension. Extend the span isometrically by an infinity-norm direct sum to dimension exactly 14 if necessary. Then 29 > 28 contradicts C(26,14)=28. This is the elementary direction of source Lemma 39; no assertion of a new bridge deserves credit.

The source already proves strong balancing cannot yield such a witness. Do not impose row sums zero. Also, a symmetric circulant 29 by 29 candidate is impossible: a nonzero constant mode gives odd rank, hence rank at most 13 if at most 14, while the source's Frobenius estimate gives rank at least 14; a zero constant mode is the prohibited balanced case. Real circulant matrices have paired conjugate frequency modes, so symmetry is not needed for this parity obstruction.

The source's Theorem 25(3), including integer rounding, already clears every relevant integer parameter in dimensions 8 through 13. In that range the conjecture has only k=2d-2, and the bound k+(1+sqrt(2d-3))/2 is strictly less than 2d+1. Searching d=8,k=14 therefore wastes effort. No new credit for these already implied cases.

## Ordinary obstruction to a tempting search template

For m=29,k=26, the sorted off-diagonal row polytope has two-valued vertices in its middle range t=3,...,24:

    a=(25-t)/(t+50), repeated t times;
    b=-t/(t+50), repeated 28-t times.

They follow by solving t*a+(25-t)*b=0 and (t-2)*a+(28-t)*b=-1. The off-diagonal squared norm is (625*t-22*t^2)/(t+50)^2, maximized among these integers at t=11; a=14/61 and b=-11/61. The row sum including the diagonal is (50-2t)/(50+t), which is positive.

A matrix with the SAME such vertex type t in every row is always nonsingular, regardless of how positive positions are permuted. Let B be the zero-diagonal 0/1 matrix of those positions; every row has t ones. Then

    (50+t) A = (50+2t) I + 25 B - t J.

On the constant line the eigenvalue is 50-2t, nonzero. On the quotient by that invariant line, singularity would require B to have the rational eigenvalue -(50+2t)/25. Since B is integral, any rational eigenvalue is integral. None of t=3,...,24 makes that number integral. Thus A has full rank 29. This rules out the natural uniform extremizer construction, not general feasible A. The quotient argument is valid because the characteristic polynomial of B on the quotient is its integer monic characteristic polynomial divided by x-t, again integer monic.

This is an ordinary diagnostic lemma, not a solution of 324209 and not a claim of literature novelty. It directs a search toward mixed or nonvertex row patterns rather than a false certificate family.

## Exact next Pi task after source qualification

Provider/model fixed by user: Pi spark/GLM-5.3-Flash-EXL3, high thinking. No task was launched here.

1. Independently audit Lemma 39 and the d=14 parameter calculation. Check source and citing works for already printed low-rank matrices. Read the actual publisher body if lawfully available, and refresh complete relevant Omega subtrees at its current HEAD. Do not infer clearance from cached old subtrees.
2. Only then perform a bounded feasibility diagnostic for rank factorization A=UV, excluding balanced and uniform-vertex/circulant ansatzes above. No all-graph or unbounded sweep is justified. Cap at two CPUs, 120 CPU seconds, 140 wall seconds and sampled RSS 6 GiB; report exhaustion candidly.
3. A success artifact must be exact rational U,V (812 entries), and optionally A (841 entries), numerator/positive-denominator pairs. No floating point matrix or small singular values qualify. Check UV=A by rational arithmetic; diagonal and bounds exactly.
4. To check all subset sums, compute each row sum s_i and all unordered triples T of columns. Verify -1 <= s_i-sum(A_ij,j in T) <= 1. There are C(29,3)=3654 triples, hence 105966 rational interval checks. These are exactly the 26-subsets by complementation, with no probabilistic coverage gap.
5. If a certificate survives, implement the finite checks and normed-space bridge in Lean, using only allowed axioms. Reconstruct rational certificates with kernel arithmetic; no native_decide. Source fidelity, significance and prior-art reviews still precede credit.

No concrete optimizer initialization or feasible factorization is currently known. A negative bounded diagnostic would not prove the conjecture. The full missing mathematical lemma is existence of such a low-rank nonbalanced matrix, or alternatively a rank-at-least-15 theorem for the entire row-feasible domain.
