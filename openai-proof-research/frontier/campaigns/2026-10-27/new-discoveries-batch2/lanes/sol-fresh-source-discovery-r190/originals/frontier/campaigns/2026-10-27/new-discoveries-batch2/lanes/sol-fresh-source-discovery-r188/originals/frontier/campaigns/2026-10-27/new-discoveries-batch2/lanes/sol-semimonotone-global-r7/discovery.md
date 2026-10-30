# Full Conjecture 3.12: unresolved; singular branch reduced to directed metrics

29 October 2026 UTC. Solo research, credit 0; no acceptance authority. The assigned
full Chauhan–Dubey conjecture remains unresolved. No PROOF.md, Lean, paper or
candidate acceptance is claimed. Counts remain 3/30 additional, 33/60 total.

## Source and eligibility

The actual retained arXiv:2603.00639v1 body was read at Theorem 2.2,
Definition 3.7, Theorem 3.9 and Conjecture 3.12. The literal question is:
for every real n-by-n A, n>=3, with every principal (n-2)-block E0 and every
principal (n-1)-block non-E0, prove det A<0 and A inverse Z. The full matrix
is automatically non-E0 by heredity. E0 means every nonzero x>=0 has a
positive coordinate i with (Ax)_i>=0. The preliminary almost-E0 prose has
swapped strict/non-strict inequalities; the literal definition and given
Theorem 2.2 are used, not those swapped inequalities.

Live arXiv abstract retrieval at 2026-10-29T05:17:58Z agrees byte-for-byte with
the preceding lane's receipt: only v1, submitted 2026-02-28 13:14:26 UTC.
The journal appeared 2026-02-27, DOI10.1080/03081087.2026.2636706. Its actual
body remains unread after the earlier403; no request was made to that host.
Fresh targeted public search found the paper and indexed MathDB373375 open
record, no resolution. This is not novelty clearance. No MathDB request was
made, respecting prior403. No GitHub API requests: the recent complete trees
and head receipts in sol-fresh-analysis-discovery-r7 were reused. The r6
registry screen has no relevant paths; current evidence is bounded path and
catalogue coverage from 04:39–04:43 UTC, not a new content-complete audit.

Root's closest-source gaps remain: Nabben1997 abstract only;
Tsatsomeros–Wendler2019 supplied inverse theorem credited; Wendler2019 full
body inaccessible (prior405); Chauhan–Dubey2023/2024 full bodies unread.
Their indexed statements do not justify the determinant-sign conjecture for
arbitrary almost-E0 matrices. No determinant sign is imported from it.

## Independent validation of root reduction

I checked the ordinary reasoning, not just root's finite tests. In its mixed
diagonal case the two diagonal Schur inequalities force equality of the
opposite-entry product with b_ii*b_jj. If b_ji/b_ii>0 the two row inequalities
are reverse bounds, hence give proportional rows; if negative, transpose
makes the needed ratio positive. Positive diagonal normalization is by positive
row scaling. For a positive pair of product p, p=1 gives proportional rows;
p>1 and x<=y<=p*x force x>=0; diagonal pair bounds exclude zero. Thus the
positive-diagonal alternatives are all-positive or strictly negative offdiagonal.
For negative diagonal normalized to -1, a positive b_12 forces the opposite
sign product b_1k*b_k2<0. In the first sign case the root inequality chain
forces b_2k*b_k2=1 with both entries negative; the paired row bounds force
proportional rows. Transposition covers the second case. These arguments
are valid for n>=3. They do not give determinant sign.

The inverse block identity identifies each single-pivot Schur complement of
B=A^-1 with A(i)^-1, when A is invertible. The rank-one perturbation proof
also checks: C_i<=0 nonsingular implies C_i*u<0 and v^T*C_i<0 for positive
u,v; Sherman–Morrison therefore makes local inverses strictly negative for
small positive perturbations. E0 on smaller blocks is preserved (indeed becomes
strict E) by positive rank-one addition. A nonzero adjugate pairs nontrivially
with some positive u,v, so generic singularity removal is valid. Common
maximal-minor sign follows. Both exact root countermodels were independently
replayed by check.py. None establishes the full conjecture.

## A further necessary condition for any singular candidate

Assume only that A is singular and every A(i) is invertible with A(i)^-1<=0.
Then rank A=n-1. All diagonal entries of adj A are nonzero. The same positive
rank-one perturbation and trichotomy prove their common sign; this does not
need the smaller-block E0 condition.

In fact adj A is either strictly positive or strictly negative entrywise.
To see this, choose a perturbation making A_e invertible for all small e>0.
Then e*A_e^-1 tends to a nonzero scalar multiple of adj A, a rank-one matrix
R with nonzero diagonal. Every entry of R is nonzero: R=u*v^T and each u_i*v_i
is nonzero. Along a sequence use one fixed trichotomy alternative. The
all-positive and all-nonpositive alternatives give constant entry sign in
the limit. The remaining alternative would give positive diagonal and strictly
negative offdiagonal in R. This is impossible in rank one for n>=3:
R_12*R_23*R_31=R_11*R_22*R_33, but the two sides would have opposite signs.
Consequently A has strictly positive right and left null vectors u,v.

Positive diagonal scaling M=diag(v)*A*diag(u) now gives M*1=0 and 1^T*M=0.
It preserves E0 on every principal support and preserves the local inverse
inequalities. Thus any singular counterexample can be assumed balanced.
This is a helper reduction, not a source resolution or discovery nomination.

## Exact parametrization of the balanced singular local condition

Let M be real, balanced, rank n-1, with kernel span(1). Put
J=I-11^T/n and G=(M+11^T/n)^-1-11^T/n. Then MG=GM=J and G1=G^T1=0.
For i deleted, direct multiplication gives

    M(i)^-1[j,k] = G_jk-G_ji-G_ik+G_ii.                    (1)

For example extend a grounded vector by zero at i, apply MG=J, and subtract
the i-th row to verify the identity; M(i) is invertible since all cofactors
are pseudodeterminant(M)/n, nonzero.

Define q_jk=G_jk-G_jj. Equation (1) says exactly

    q_jk <= q_ji+q_ik   for every i,j,k.                  (2)

The cases i=j or i=k are equalities; the diagonal cases supply the round-trip
nonnegativity. Also q_jj=0. Although q may have negative entries, fix r and
set d_jk=q_jk+q_rj-q_rk. Triangle inequality makes every d_jk>=0;
d still satisfies (2), has zero diagonal, and J*d*J=G. Thus d is a directed
semimetric (zero distances between distinct points are allowed).

Conversely take any such directed semimetric d for which J*d*J is invertible
on 1-perp. Set G=J*d*J and M=(G+11^T/n)^-1-11^T/n. Then M is balanced
rank n-1 and (1) equals d_jk-d_ji-d_ik<=0. This proves an exact ordinary
parametrization of singular matrices satisfying all local inverse signs,
after the positive scalings above. It makes the missing source step precise:
one must show this inverse construction ALWAYS has a non-E0 principal
(n-2)-block. That assertion is not proved here. The directed semimetric is
not forced symmetric; discarding its antisymmetric part loses information.

When M is symmetric one may choose the symmetric semimetric
D_jk=2G_jk-G_jj-G_kk. Then
M(i)^-1[j,k]=-(D_ji+D_ik-D_jk)/2 and M=2*(JDJ)^-1 on 1-perp.
Triangle inequalities explain all local inverse signs without numerical
optimization. These are ordinary matrix identities; no originality is
asserted for the general metric/Green-matrix connection.

## New exact singular obstruction to the weakened hypotheses

Split six indices into groups of three. Set A diagonal1/3, within-group
offdiagonal7/3, cross-group-5/3. Then

* A1=0, rank A=5; eigenvalues are 0,10,-2,-2,-2,-2.
* Every maximal principal minor is 80/3, positive.
* All maximal blocks have entrywise nonpositive inverse.
* Every diagonal entry of A is strictly positive.

An exact certificate is the six-point metric D with within-group distances1
and cross-group distances3/5. It satisfies triangle inequalities; the grounded
inverse formula above verifies every local inverse. Each maximal block maps
a strictly positive vector to minus ones (the retained vectors have coordinates
3 on the other two indices in the deleted index's group and9/5 on the other
group). Thus all maximal blocks and A itself fail E0.

This construction is singular, unlike both root examples. It decisively rules
out proving nonsingularity from local inverse signs, common nonzero cofactor
sign, positive left/right kernels, symmetry, and positive A diagonal alone.
It is NOT an E0_2 counterexample: a cross-group pair sends ones to
(-4/3,-4/3); the four-block with two indices per group sends ones to
-2/3 ones. Hence the load-bearing smaller-block E0 condition fails explicitly.
This obstruction is new in these lane notes, not a literature novelty claim.

## Failed routes, checks, and precise remaining work

The metric route supplies an exact parametrization but does not force E0 on
smaller blocks, nor contradict it. Positive diagonal and positive kernel do
not exclude singularity, as the exact example demonstrates. A bounded random
metric probe (2000 each at n6,8,10, distances integer10..20 so triangles hold)
found6000 invertible borders,24 positive-diagonal inverse constructions, and
zero passing pair E0. Floating condition thresholds and the distribution make
this only diagnostic; it proves neither pair obstruction nor the conjecture.
No unbounded search or optimization was run. A conjecture that every metric
inverse with nonnegative diagonal already fails pair E0 remains UNPROVED and
is not used. In the nonsymmetric problem quadratic-form/copositive reasoning
cannot replace E0.

Exact check.py verifies the singular fixture, rank/cofactors, all six inverse
identities, witnesses, both root countermodels, and one nonsymmetric directed
semimetric fixture. The initial checker guessed the singular cofactor as-64;
its assertion failed before any result output. Recomputing from the displayed
eigenvalues gives80/3; the corrected retained checker passes. Initial optional
HTML parsing failed because bs4 was unavailable; built-in/regex source reading
was used, without dependency installation.

Run `python check.py` and `python metric_probe.py` from this lane. Each sets
BLAS/OMP/MKL1 before imports and RLIMIT_AS512MiB; CPU caps35s and25s respectively.
No exponential support traversal is used. These checks do not certify a full
ordinary source theorem, measured RSS, formal endpoint, or novelty.

Still missing: source nonsingularity using ALL (n-2)-E0 hypotheses; negative
determinant without Wendler's unproved claim; exclusion of the positive inverse
branch. Actual journal and closest companion-body comparisons remain access
and novelty gaps. Major Lean investment would be premature.
