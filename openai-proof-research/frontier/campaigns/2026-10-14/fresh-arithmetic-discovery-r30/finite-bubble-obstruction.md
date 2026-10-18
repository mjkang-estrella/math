# A finite bubble budget cannot repair the global stability screen

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

**Status: technical screening evidence, not a candidate or a new finding.** The scalar two-bump obstruction was already proved in `frontier/iterations/i38-inequality-stability-discovery.md`, §1.2. The argument below records its elementary finite-budget extension and makes no substantiality or priority claim. No full research target was frozen in r30. The stipulated source is family262 at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

## Exact notation and statement

Fix any real gamma in (1/2,3/2). Write p=gamma+1/2, r=(gamma−1/2)^−1 and

    w_(a,b)(x)=(r+1)a² sech²(ra(x−b)),  a>0, b∈R,
    w=w_(1,0),  M=integral_R w^p=1/C_gamma.

The last equality and the fact that −1 is the sole negative eigenvalue of −∂²−w are supplied by the pinned equality manuscript, `thm:main` and `rig:factorization`–`rig:partner` with the final normalization calculation. Let B_K be the set of sums of at most K such nonnegative scalar solitons, with arbitrary scales and centers. The zero sum is allowed; there is **no normalization constraint on an approximant**. Set B_0={0}.

For every pair of fixed integers k>K≥0, put

    V_L(x)=sum_(j=1)^k w(x−jL),       L>0.

Then

    integral V_L^p → kM,
    Tr(−∂²−V_L)_−^gamma → k,
    inf_(B∈B_K) ||V_L−B||_p^p → (k−K)M.                 (1)

For t_L=(integral V_L^p)^−1/(2gamma) and U_L(x)=t_L² V_L(t_L x),

    integral U_L^p=1,
    1−C_gamma^−1 Tr(−∂²−U_L)_−^gamma → 0,
    inf_(B∈B_K) ||U_L−B||_p^p → (k−K)/k.               (2)

These assertions are for scalar potentials. They already obstruct any proposed bound required uniformly over all finite matrix sizes. They do not obstruct a bubble family with unrestricted cardinality or a theorem with extra spectral information.

## Proof of the norm and spectral limits

For a fixed k, approximate w in L^p by a bounded compactly supported function. Its k translates have disjoint supports for large L. The triangle inequality bounds the error of the sum by k times the single-profile approximation error, independently of L. Sending that error to zero proves the first limit in (1). This argument also proves that deleting any fixed K of the k wells leaves p-th power norm tending to (k−K)M.

Let psi be the normalized one-well ground state, proportional to sech^(1/r)(rx). Compactly supported smooth truncations approximate psi in H^1 and have Rayleigh quotient for −∂²−w tending to −1. Given epsilon>0, choose one normalized truncation with quotient at most −1+epsilon. For all sufficiently large L, its k translates have disjoint supports. The quadratic form of −∂²−V_L on their span is diagonal, since the supports are disjoint. Each diagonal entry is at most −1+epsilon: the other nonnegative wells only decrease it. The min–max principle therefore gives k negative eigenvalues at most −1+epsilon, and hence

    liminf_(L→∞) Tr(−∂²−V_L)_−^gamma ≥ k.

The stipulated scalar inequality gives the reverse limsup because C_gamma integral V_L^p→k. This controls the **full** negative spectral moment without asserting that V_L has exactly k negative eigenvalues. No threshold eigenvalue is discarded. Letting epsilon decrease to zero proves the second limit in (1).

## Proof of the sharp distance limit

The upper bound follows by choosing B equal to any K of the displayed wells. For the lower bound it suffices to consider arbitrary sequences L_n→∞ and B_n∈B_K whose distances to V_(L_n) are bounded. Write

    B_n=sum_(i=1)^K w_(a_(i,n),b_(i,n)),

padding with zero terms when necessary. Since each summand is nonnegative,

    ||w_(a_(i,n),b_(i,n))||_p ≤ ||B_n||_p
      ≤ ||V_(L_n)||_p+||V_(L_n)−B_n||_p.

The right side is bounded. Since the p-th power norm of one summand is M a_(i,n)^(2gamma), all scales are bounded above. Pass to a subsequence on which every scale has a limit. A term whose scale tends to zero has global L^p norm tending to zero and may be omitted for the lower bound. For each remaining term, its scale lies in a compact subinterval of (0,infinity).

For each remaining term i and each well j, pass to a further subsequence on which b_(i,n)−jL_n either converges to a finite real value or diverges in absolute value. There are finitely many pairs, so this can be done simultaneously. Each term can have finite displacement from **at most one** well because distinct well centers separate by L_n. Consequently at least k−K wells have divergent displacement from every remaining term. Call any k−K of them unmatched.

Fix R>0. On the interval jL_n+[−R,R] about an unmatched well, every positive-limit-scale approximant tends uniformly to zero: sech² has uniform decay for scales in a fixed compact subinterval of (0,infinity). The zero-limit-scale terms tend to zero in L^p globally. The other k−1 wells in V_(L_n) likewise tend uniformly to zero on this interval. Thus

    integral_(jL_n−R)^(jL_n+R) |V_(L_n)−B_n|^p
       → integral_(-R)^R w^p.

The unmatched intervals are disjoint for large n. Summing, taking the lower limit and then R→∞ gives the lower bound (k−K)M. This holds along a subsequence realizing any proposed lower limit, proving the final limit in (1). The proof explicitly handles varying centers, vanishing scales, arbitrarily narrow profiles, and cancellation: narrow profiles have already been excluded by the norm bound, and positivity is what bounds each summand by the whole approximant.

Finally, the Schrödinger dilation f(x)↦t²f(tx) multiplies both the p-th power norm and the gamma-moment by t^(2p−1)=t^(2gamma). It maps B_K bijectively onto B_K. Applying it with t=t_L proves every assertion of (2).

## What this excludes, and what it leaves unpaid

For every fixed integer K≥1, take k=2K. Arbitrarily small normalized full-moment deficit is compatible with distance approaching 2^(−1/p) from B_K. More generally, for every positive deficit tolerance delta and every finite proposed budget K, there exist normalized potentials with deficit below delta whose distance to B_K is bounded below, say by 4^(−1/p). Thus a stability statement of the form “all potentials with deficit at most delta can be approximated by at most K(delta) bubbles within an error tending to zero” fails for every finite-valued K(delta). This uses a tolerance upper bound, not a claim about a prescribed exact deficit value.

A bound on physical channel dimension cannot supply the missing budget: every example here has one channel. A fixed truncation rank N in the spectral objective is different data. No matrix bubble decomposition, scale-uniform compactness theorem, quantitative spectral tail theorem, or stability theorem to the union of **all** finite bubble sums is proved. The finite-budget obstruction is not evidence against those statements, nor against the pinned sharp inequality/equality theorem.

## Attribution and operation comparison

I38 already contains the two-bump construction, normalization, min–max sandwich and positive distance from one exact equality profile. The k/K argument is an elementary extension of that operation, not a new research mechanism.

Frank–Gontier–Lewin, *Optimizers for the finite-rank Lieb–Thirring inequality*, [arXiv:2109.05984v2](https://arxiv.org/html/2109.05984v2), Theorem1, gives translation-separated bubbles for a fixed-rank maximizing sequence, with positive integer spectral ranks summing to N. Its hypotheses retain a fixed N. Their compactness regime in Theorem4 is gamma>3/2 in dimension one. Neither statement is an unrestricted finite-budget stability assertion in the present exponent range. Theorem1 and its surrounding discussion were read; its full proof was not read or used here.

The pinned equality compactness proof fixes W and its eigenfunctions. The Gram interval used to bound each coefficient row depends on those fixed eigenfunctions; its tail bound uses both fixed physical dimension m and decay of that fixed spectrum. The finite-interval action defect has a coefficient independent of row/column count, but it controls auxiliary action relations. These are credited source operations, not a global distance estimate or a uniform bubble budget. Their validity is stipulated, not audited.
