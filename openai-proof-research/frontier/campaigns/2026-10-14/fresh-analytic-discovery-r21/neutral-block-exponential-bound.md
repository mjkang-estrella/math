# A technical exponential-moment refinement of the source energy argument

Myeongjin Kang; no affiliation. Original prose CC BY4.0.

This is a proved author-level technical deduction, not a substantial-result nomination. Fix c in (0,2); constants may depend on c and on A. No assertion uniform in c or at c=2 is made here. All notation and operator-domain inputs are those of pinned Section7, Lemma ordinary-moments. Their truth is stipulated.

## Claim and proof

Under the three conditions (prob-g-conditions), with R>=1 and D=sum_l g_l Z_l, there is B=B(A,c)<infinity such that

    ||D||_(L^q(P_c)) <= B q   for every real q>=1,
    E_c exp(|D|/(2eB)) <= 2.

The source proves ||D B_1||=||B_1 D||<=C_A, where B_1=1_{E<=1/R} on the spin subspace and E Omega=0. This bound is independent of the moment order. It also identifies the link-exchange expression for the double commutator of D^k. Its coefficient loss can be tracked explicitly instead of denoted C_(A,k).

Put a=D and b=D^(sw,l) in the common site-diagonal representation. Since |a-b|<=2|g_l-g_(l+1)|<=2A, polynomial factorization gives, for every integer k>=1,

    |a^k-b^k|^2 <= k^2 |a-b|^2 max(|a|,|b|)^(2k-2)
                  <= 4 k^2 |g_l-g_(l+1)|^2 (|D|+2A)^(2k-2).

The actual square multiplier is invariant under the exchange and therefore commutes with that norm-one involution. The source's absolute-value estimate bounds the exchange expectation by the expectation of this multiplier. The local link coefficients have a bound depending only on c. Summing links, using sum_l |g_l-g_(l+1)|^2<=A/R, and the exact double-commutator identity yields

    <D^k Omega,E D^k Omega> <= (C_A k^2/R) E (|D|+2A)^(2k-2).             (1)

All domain passages are precisely the source's fixed-local-power passages; for each finite support D is a bounded operator, so all moments in this argument are finite before taking uniform bounds.

Write m_k=E|D|^(2k). The low-band component has squared norm at most C_A^2 m_(k-1), while its orthogonal complement has squared norm at most R times (1). Enlarging a constant C independent of k gives

    m_k <= C k^2 E (|D|+2A)^(2k-2).                                    (2)

For k=1 the right side is C. Choose B_0>=max(2A,sqrt(C)). Inductively assume ||D||_(2k-2)<=B_0(k-1). Minkowski and (2) give

    m_k <= C k^2 [B_0(k-1)+2A]^(2k-2)
         <= C k^2 (B_0 k)^(2k-2) <= (B_0 k)^(2k).

This includes the initial k=1 case. Thus ||D||_(2k)<=B_0 k. For real q>=1 choose k=ceil(q/2)<=q; monotonicity of probability-space norms gives ||D||_q<=B_0 q. Take B=B_0. Finally, using q! >= (q/e)^q for integer q>=1 and monotone convergence,

    E exp(|D|/(2eB))
      <= 1 + sum_(q>=1) (Bq)^q / [(2eB)^q q!]
      <= 1 + sum_(q>=1) 2^(-q) = 2.

## Neutral spatial blocks

For a density f supported in a square of side Ar, with integral zero and |f|<=Ar^(-2), the source's proof of Corollary neutral-blocks decomposes the pairing into O(R) column contributions of L^q size at most Cq/R, followed by a horizontal average of the same type, where R=r/delta>=1. Minkowski's inequality preserves the linear q dependence. If r<delta, the original unit-jump bound is deterministic. Consequently there is B'=B'(A,c) such that, uniformly in location, r and delta,

    ||<h_delta,f>||_q <= B' q,
    E exp(|<h_delta,f>|/(2eB')) <= 2.                                  (3)

No separation, independence, conditional estimate or Gaussian tail is claimed.

For a fixed compactly supported smooth neutral f, source smooth-test convergence and (3) imply convergence of Laplace transforms in some fixed neighborhood of zero. Indeed choose the argument strictly inside the exponential-integrability radius and use a slightly larger exponent for uniform integrability. The same applies to finite fixed linear combinations. This is a direct moment refinement, not a new continuum identification.

## Exact limitation for microscopic exponentials

If a height average at scale r is pinned to a fixed macroscopic average, the source telescopes J=O(1+log(1/r)) neutral blocks. Minkowski gives only ||X||_q<=CB' qJ. Hölder likewise controls exp(s sum_j B_j) through the marginal estimates (3) only when |s|J is within their fixed radius. Thus the paid inference gives an exponential-moment neighborhood shrinking like 1/J. It does not yield fixed-charge Gaussian asymptotics as J tends to infinity.

The source separated-block lemma does not close this issue: it requires the selected center to be a positive distance from every other factor center. Successive radial scales around one point have the same center. The new exponential bound therefore cannot silently be iterated as a conditional or independent bound. A multiscale tilted estimate remains unpaid.
