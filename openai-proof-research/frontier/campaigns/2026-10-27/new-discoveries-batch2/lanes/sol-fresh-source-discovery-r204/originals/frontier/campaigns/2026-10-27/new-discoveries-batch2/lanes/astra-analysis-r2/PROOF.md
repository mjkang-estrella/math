# Kellner identity: EXCLUDED as already proved

Source: B. C. Kellner, arXiv:2509.05235v1, Theorem 4.1 equations (4.1)--(4.2), Remark 4.5, Conjecture 4.6. The current abstract page lists only v1. Disposition: EXCLUDE. Matsuno arXiv:2607.10106v1 Theorem 1.3 and Corollaries 1.7, 3.1 already give the same complete result. Actual body and proof read. No novelty, full Lean, or acceptance claim. The derivation below was found independently before locating this successor.

Let R=Q[X_1,X_2,...]. For n>=1 put h_n=sum_{j=1}^n (-1)^(j+1)X_j/j. Let psi_n be the source's exact triangular recurrence, psi_0=0. Then the proposed all-variable identity is

    psi_n = -B_n(-1! h_1, -2! h_2, ..., -n! h_n).

Equivalently, if A(t)=sum_{n>=1} psi_n t^n/n! and H(t)=sum_{j>=1}(-1)^(j+1) X_j t^j/j, then

    A(t)=1-exp(-H(t)/(1-t)).

All identities below are formal, so no convergence assumptions on X are needed. Every coefficient uses finitely many terms.

## Complete ordinary proof

Write S(t)=sum_{n>=1} sigmahat_n^star t^n/n!. The source formula for sigmahat and the defining Bell generating function give

    1+S(t)=exp(H(t)).

For the source's correction polynomial Psi_n, use the defining partial Bell identity

    A(t)^nu/nu! = sum_{r>=nu} B_{r,nu}(psi_1,...,psi_{r-nu+1}) t^r/r!.

Multiplication by t^k and coefficient extraction gives precisely the factor (n)_k B_{n-k,nu} in source (4.2). Also the source uses signed Stirling numbers, and

    sum_{k=0}^nu s(nu+1,k+1)t^k=(t-1)(t-2)...(t-nu).

Thus, coefficientwise summing the source correction gives

    sum_{n>=1} Psi_n t^n/n!
      = sum_{nu>=2} (-1)^(nu+1) binom(t-1,nu) A(t)^nu
      = 1-(1-A(t))^(t-1)-(t-1)A(t).

The formal variable exponent is defined by exp((t-1)log(1-A)); the generalized binomial identity follows first with an independent indeterminate exponent u over Q[u], then substituting u=t-1 coefficientwise. Since A has zero constant coefficient this substitution and the displayed infinite sums are legitimate in the t-adic topology.

The source recursion psi_n=n psi_(n-1)+sigmahat_n^star+Psi_n now sums to

    A=t A+S+1-(1-A)^(t-1)-(t-1)A.

Cancel A to obtain (1-A)^(t-1)=1+S=exp(H). Apply the formal logarithm on 1+tR[[t]]; (t-1)log(1-A)=H. Since 1-t is a unit, log(1-A)=-H/(1-t), hence A=1-exp(-H/(1-t)). Finally [t^n]H/(1-t)=h_n and the complete Bell definition gives the claimed formula. The source recurrence is triangular (nu>=2 means only psi_i with i<n occur), so it defines a unique family. No other solution branch is present.

## Source Conjecture 4.6

Under X_j=epsilon for every j, where epsilon is +1 or -1, h_n=epsilon*Hbar_n and H(t)=epsilon log(1+t). Consequently

    psi_n(epsilon,...,epsilon)=-B_n(-epsilon 1! Hbar_1,...,-epsilon n! Hbar_n),
    sum psi_n(epsilon) t^n/n! = 1-(1+t)^(-epsilon/(1-t)).

These are both source statements for every n>=1, as formal Taylor identities. Analytically the right side is holomorphic for |t|<1 using the branch log(1+t) with value zero at t=0, so its Taylor coefficients are the same. No claim about the radius being exactly one is needed.

## Formal scope and disposition

No acceptance gates will be pursued: this entire source family is already resolved by Matsuno. The initial Lean module proves only explicit coefficient nonvanishing, a ring cancellation, and one finite polynomial identity; it does not prove the source recurrence/series bridge. No full-source certificate, paper or packet is claimed.

## All monomial coefficients and exact support

The same identity gives more than the two specializations. Fix a finite sequence of nonnegative integers m=(m_1,...,m_n), not all zero. Set

    d=sum m_j,  w=sum j*m_j,  z_m=product j^(m_j)*m_j!.

Then

    [X_1^m_1 ... X_n^m_n] psi_n
      = (-1)^(w+1) (n!/z_m) binom(n-w+d-1,d-1), if 1<=w<=n;
      = 0, if w>n.

The constant coefficient is zero. To prove the formula, write

    exp(-H(t)/(1-t))
      = product_{j>=1} exp((-1)^j X_j t^j/(j(1-t))).

The coefficient of X^m in this product is

    (-1)^w t^w / (z_m*(1-t)^d).

The negative sign in A=1-exp(...) and the ordinary negative-binomial expansion finish the proof. Formal products are locally finite, since X_j first occurs at t^j. Every coefficient with 1<=w<=n is nonzero: n! and z_m are positive and binom(n-w+d-1,d-1)>0. Thus the exact support is ALL nonempty partitions of each weight 1,...,n, with signs determined solely by the parity of weight. In particular,

    #psi_n = sum_{w=1}^n p(w),

which makes the source Theorem 1.3 upper bound an equality in every degree. This is an all-variable formula, not a numerical or parameter-specific observation.

## Source Remark 4.5: all weight statements

Let weight(X_j)=j. Write C_{n,k}=B_{n,k}(psi_1,...,psi_{n-k+1}). In the coefficient of X_1^n only top-weight parts can contribute. Those parts, after all other X_j are set to zero, have exponential generating function 1-exp(-X_1*t). Therefore

    [X_1^n] C_{n,k} = (-1)^(n-k) S_2(n,k).

Proof: C_{n,k}=n![t^n]A(t)^k/k! and
(1-exp(-u))^k/k!=sum_{n>=k}(-1)^(n-k)S_2(n,k)u^n/n!, the standard Stirling identity. The lower-weight pieces cannot contribute X_1^n at order t^n. This coefficient is nonzero for 1<=k<=n, so the source weight upper bound is attained.

For Psi_n=psi_n-n psi_(n-1)-sigmahat_n^star, the middle term has weight<=n-1. If w=n, the source sigmahat has coefficient (-1)^(n+d)n!/z_m. Thus

    [X^m] Psi_n = (-1)^(n+1)(1+(-1)^d)n!/z_m  (w=n).

For even n>=2 choose X_1^n: the coefficient is -2. For odd n>=3 choose X_1^(n-2)X_2: the coefficient is n(n-1). Hence weight(Psi_n)=n for all n>=2, resolving the other assertion in Remark 4.5. These consequences belong to the same proposed source family; no separate outcome counts.
