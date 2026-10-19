# Family175: coordinatewise product costs do not leave a new mechanism

This pre-freeze feasibility calculation explains why a heterogeneous-probability extension was not selected. It is author analysis, not an independent proof gate or a substitute nominee.

The contemplated extension keeps the source's `k=2^75` and replaces one Bernoulli parameter by a vector `(p_i)` with every `0<p_i<1`. The family D is arbitrary, including nonmonotone families; repetitions in unions remain allowed. The screened conclusion is that `mu_p(D)>=1-1/k` gives a containment cover of `E_k(D)` of product cost at most1/2, where a generator I costs `p(I)=product_(i in I) p_i`. It does **not** reduce k to two and does not claim a new random-containment threshold.

The actual paid source proof, rather than just its constant-parameter theorem statement, gives the following compatible calculation. Put `L=2^70`.

## The weighted covering operation

For a positive vector rho with entries below1, set `rho(I)=product_(i in I)rho_i`. In `01_covering.tex`, replace `|H| rho^r` by `sum_(e in H)rho(e)` for an r-uniform edge family. Define

    d(I) = sum_(e in H, I subset e) rho(e minus I).

The source's two identities become, without losses,

    sum_I rho(I)d(I) = 2^r sum_e rho(e),
    sum_(e regular) rho(e minus B) <= T sum_(j=0)^r binom(|B|,j).

The second identity groups edges by the **exact** intersection `I=e intersect B`; then `rho(e minus B)=rho(e minus I)`. Large-degree generators therefore have the same cost bound. Sampling ordered edge pairs still has expectation bounded by `pi sum_e rho(e) 2^r T`. For residual tuples, multiplicativity gives

    rho(B union e) = rho(B) rho(e minus B).

Consequently the same prefix extension recurrence, the same `m^2` independent ordered-pair sampling indices, and the same residual bound apply. The numerical choices `m=2^(12h), T=2^(4h), pi=2^(-8h)` are unchanged. This is the source's existing weighted-degree operation expressed with product costs; it requires no independence between intersecting edge events.

## Signed coefficients and bins

For arbitrary vector q in `(0,1)^X`, let `f=1_F` and define

    b(U) = product_(i in U)(1-q_i) * sum_(z in {0,1}^U)(-1)^|z| E[f(z,Y)],
    w(U) = b(U)^2,

with the product-q exterior law. The tensor product of the one-coordinate biased bases gives

    sum_U q(U) w(U)
      = sum_U product_(i in U)(1-q_i) * fhat(U)^2 <= 1.

For an exceptional set not covered by32 members, use in column i the source's signed correction

    R_i(y) = product_(j=1)^32 q_i^y_j (1-q_i)^(1-y_j)
             - (1-q_i)^32 (-1)^(sum_j y_j).

The all-zero column has weight zero. Expansion and pointwise vanishing give exactly `sum_(U subset S)(-1)^|U| b(U)^32=0`, hence `sum_(nonempty U subset S)w(U)^16>=2^-32` when `mu_q(F)>=1/2`.

Taking `rho_i=q_i/L` gives `rho(U)=q(U)L^-|U|`. Thus the source's large-weight cutoff `w(U)>=2^(-64|U|)`, the same `(r,h)` weight bins, the weighted covering operation above, and both geometric sums remain compatible. In a bin the needed bound is now `sum_(e in H_(r,h))rho(e)<=2^(h+1)`, precisely the hypothesis that the preceding calculation permits. The constant-density-loss operation is unchanged.

## The mixed saturated-coordinate case

Simply quoting the source's two scalar cases would omit the case where some `Lp_i` are below1 and some exceed1. It is still paid by the actual coordinatewise coupling.

Independently across i, make L rows. If `Lp_i<1`, assign i to one uniformly chosen row with total probability `Lp_i` and to no row otherwise. If `Lp_i>=1`, choose one mandatory row uniformly and independently add i to each other row with probability `(p_i-1/L)/(1-1/L)`. Each complete row has exactly the original product law, and their union has independent coordinates with probabilities `q_i=min(Lp_i,1)`. A union bound gives probability at least31/32 that all rows lie in D.

Let S0 be the saturated coordinates and X0 the others. Let F be the family of unions of L members of D, and define

    F0 = { A subset X0 : S0 union A belongs to F }.

The union law gives `mu_(q|X0)(F0)>=31/32`. If X0 is empty, F contains the whole ground set and the exceptional family is empty. Otherwise apply the already checked product-cost half-density calculation on X0. If T is exceptional for32 unions from F, then `T intersect X0` is exceptional for32 unions from F0: a cover of that projection by F0 members lifts to a cover of T by their unions with S0. The resulting generators lie in X0 and cost exactly `product_i p_i`, because `q_i/L=p_i` there. Finally `E_32(F)=E_(32L)(D)`, by grouping and expanding tuples as in the source.

This closes the only apparent compatibility issue of this parameter extension; it does not produce a distinct unpaid structural operation. It was screened out before a target freeze.

## Primary and historical boundaries

Li's *On p-Spread Measures* was read in both v1 and v2 at the kernel/diagonalization proof. The successful newer version is `2609.08967v2`: Theorems1.14–1.15 and Lemmas2.4–2.5 distinguish a no-spread-measure statement from fractional cost1/2. Its two-row kernel and tensorization are credited antecedents, as the pinned source itself says. We do not relabel the source's32-row operation as new. Pham `2412.03540v2`, Section3, supplies the actual equal-distribution-of-weight rounding calculation; the pinned rounding paper already changes its finite-support bound using the simultaneous selector. The source companion's two-union corollary already has constant density loss.

I02's transversal calculation distinguishes expectation thresholds from random containment. I60 and I62 already develop same-density **two**-union covers, including the missing integral rounding and the failed enlarged-density coefficient estimate. None of that unresolved target is repaired by the calculation here. The graph-decomposition companion's `cor:typical-cover` and its explicit warning that piece embeddings need not agree were checked; neither globally compatible graph copies nor rooted-packing amplification is nominated.

Primary bodies: https://arxiv.org/pdf/2609.08967v2 and https://arxiv.org/pdf/2412.03540v2 . All formula adaptation above is author screening work, with no claim of worldwide novelty or independent certification.
