# 336597: ordinary proof, specific prior HOLD, zero credit
Author reasoning only, not an independent validation or acceptance. No mathematical software used. Source 1707.03459 Conjecture 1, Sections 7 and 9, was read including the unfinished proof stages. This proves the displayed kernel identity algebraically; it does not establish novelty or repair all q-matroid invariant definitions elsewhere in that paper.

Work first over K=Q(q), with q indeterminate. Put D_m=product_{r=1}^m(1-q^r), D_0=1, and
A(X,Y)=sum_{m,n>=0} q^(mn) X^m Y^n/(D_m D_n).
Let B=A^{-1} in K[[X,Y]], writing B=sum b_mn X^mY^n/(D_mD_n). Its constant term is 1.

Direct coefficient comparison gives
(1-XY) A(X,qY)=(1-Y) A(X,Y).
For m,n positive, after multiplying a coefficient by D_mD_n, the left side is
q^(mn+n)-q^(mn-m)(1-q^m)(1-q^n),
and the right side is q^(mn)-q^(mn-m)(1-q^n); expansion makes them equal. At m=0 or n=0 the same equation holds by the missing-term convention. Inverting the units gives
(1-Y) B(X,qY)=(1-XY) B(X,Y).
Consequently, for n>=1,
b_mn=(1-q^m)b_(m-1,n-1)-q^(n-1)b_(m,n-1),
where the first term is zero when m=0.

Boundary: b_m0=(-1)^m q^(m(m-1)/2). To verify, the product of sum X^m/D_m and sum (-1)^m q^binom(m,2) X^m/D_m has coefficient of X^N equal to D_N^{-1} sum_i (-1)^i q^binom(i,2) [N choose i]_q. The finite q-binomial identity makes this 0 for N>0 and 1 for N=0. This identity itself follows by induction from expansion of product_{j=0}^{N-1}(1+q^j t); its coefficient of t^i is q^binom(i,2)[N choose i]_q (Gaussian Pascal recurrence proves the induction). Evaluate at t=-1. This pays the boundary without an infinite-product convergence assumption.

Write b_mn=(-1)^(m+n)f_mn. The recurrence becomes
f_mn=(1-q^m)f_(m-1,n-1)+q^(n-1)f_(m,n-1).
Claim f_mn=q^binom(|m-n|,2)(1+q^|m-n|-q^max(m,n)).
Its n=0 boundary is q^binom(m,2); m=0 similarly follows from the recurrence. Induct on n, simultaneously for every m. For m>=n>=1 put d=m-n. Factoring q^binom(d,2), the recurrence's right side is
(1-q^m)(1+q^d-q^(m-1))+q^(m-1)(1+q^(d+1)-q^m)
=1+q^d-q^m.
For n>m>=1 put d=n-m>=1. Factoring q^binom(d,2), its right side is
(1-q^m)(1+q^d-q^(n-1))+q^m(1+q^(d-1)-q^(n-1))
=1+q^d-q^n.
Thus the formula holds for all nonnegative m,n. No negative exponent is needed in these factorizations, including d=0 and d=1.

For target endpoints e<=a, f<=b set u=a-e,v=b-f and c=e+i,d=f+j. Gaussian multiplication gives
[a choose c]_q[c choose e]_q=[a choose e]_q[u choose i]_q,
and the analogous identity for b. The convolution alpha beta is therefore
[a choose e]_q[b choose f]_q sum_{i=0}^u sum_{j=0}^v [u choose i]_q[v choose j]_q q^((u-i)(v-j)) b_ij.
The sum is D_uD_v times coefficient X^uY^v in AB=1, hence delta_(u,0)delta_(v,0). The remaining prefactor is 1 on the diagonal. This is precisely alpha beta=delta with beta(a,b;c,d)=[a choose c]_q[b choose d]_q b_(a-c,b-d). Outside comparable endpoints both kernels are zero. On every finite rectangular poset alpha is unitriangular, whose inverse exists uniquely by recursive substitution; its verified right inverse is also its left inverse. This pays both convolution directions.

All final expressions are polynomials in q with integer coefficients. Identity over Q(q) implies the polynomial identity, hence specialization to each prime power q, and also q=1 if desired. No illegal specialization of the intermediate denominators is involved. This covers every nonnegative endpoint in the literal rectangular poset and all finite rho,nu.

Failed/unfinished first route: source Section 9's suggested row/column cancellations do not follow merely from the shifted one-dimensional q-binomial sum. The absolute value and max split the summation domain; claiming every row vanishes would require additional identities. I replaced that route with the functional equation above, rather than treating the printed sketch or computational experiments as proof.

Prior, novelty, significance: native search identified Byrne and Fulcher, Invariants of Tutte partitions and a q-analogue, JCTB 172 (May 2025), DOI 10.1016/j.jctb.2024.12.002, with a specific claim to prove exactly the earlier Conjecture 1. Definitions 55/57 and inversion results are the relevant unread body. Publisher GET returned 403; the entire identified work is unavailable across original/version/mirror/author/cache/DOI deliveries, including any earlier arXiv version. Search excerpts are navigation only. Thus this is SPECIFIC_PRIOR_BODY_HOLD, not an authenticated literature exclusion or novelty claim. Strongest significance case: a full explicit inverse is a genuine all-parameter algebraic endpoint, and short standard tools alone do not disqualify it. Strongest contrary case: the independently identified earlier exact proof claim would make the entire endpoint public, with zero novelty. No routine-exclusion bridge is asserted without reading that work. No FULLCANDIDATE or dormant formal plan is issued because this is not a qualified survivor. No dispatch.
