# Ordinary full-scope argument, excluded from discovery credit

Source: Shun-Wei Xu, Jun-Ling Sun, Chao-Ping Chen, *New Shafer-Fink type inequalities for inverse trigonometric, inverse hyperbolic and arc lemniscate functions*, Applicable Analysis and Discrete Mathematics 20 (2026), 81–102, DOI 10.2298/AADM250324010X. Published PDF, Conjecture 2 equation (27), p89; Conjecture 3 equation (35), p94. The published p94 upper endpoint sqrt(11445)/109 is exactly sqrt(105/109), not sqrt(11445/109). The actual functions are arctan in Conjecture 2 and arctanh in Conjecture 3; web snippets confusing these are not used.

For every real x>0,

    arctan(x) < 53x / [18 + 35(1+109x²/105)^(53/109)].       (A)

For every real 0<x<sqrt(105/109),

    arctanh(x) < 53x / [18 + 35(1-109x²/105)^(53/109)].      (H)

All powers are the positive real powers. These are precisely the complete two source claims, with no added hypothesis or deleted exception. There is no assertion here about Conjecture 1, nor any extra discovery credit for (H).

## Derivative bridge, including signs and domains

Let e=+1 for (A), e=-1 for (H), and set t=(1+e109x²/105)^(1/109), D=18+35t^53, U=53x/D. In both domains t>0, D>0, and

    e x² = (105/109)(t^109-1),
    t' = e 2x/(105t^108).

In (A), t>1. In (H), 0<t<1; also x<1 so arctanh is real and differentiable. Denote by F the corresponding arctan or arctanh, so F'=1/(1+e x²). Direct differentiation, with the factor e retained, gives

    U' = 53[D - e(106/3)x²t^(-56)]/D²
       = 53[18+(105/109)t^53+(3710/109)t^(-56)]/D²
       = 53[1962t^56+105t^109+3710]/[109t^56D²].

Since 1+e x²=(105t^109+4)/109,

    U'-F' = P(t)/[109t^56D²(105t^109+4)],

where the denominator is strictly positive and

    P(t)=584325t^218+10918530t^165-14554225t^162
         +5698350t^109-3433500t^56+786520.

## Explicit finite positivity certificate

Define binomial(a,3)=0 for integers a<3. For each integer 0<=k<=214 define

    q_k = 786520 binomial(k+3,3)
          -3433500 binomial(k-53,3)
          +5698350 binomial(k-106,3)
          -14554225 binomial(k-159,3)
          +10918530 binomial(k-162,3).

Then P(t)=(t-1)^4 sum_{k=0}^{214} q_k t^k, and every q_k is a positive integer. This is a finite exact certificate, supplied in full as certificate.json, not a floating point test on sampled t. It can be checked by the following completely specified integer procedure: compute each of the 215 displayed integers, verify each is >0, and convolve the resulting list with [1,-4,6,-4,1]. The 219 resulting coefficients are exactly those of P. The minimum is 786520. The first four entries are 786520, 3146080, 7865200, 15730400; the last is 584325. The runnable checks.py implements this procedure with Python integers and independently reconstructs the sparse derivative numerator. Thus no root isolation, rounding estimate or infinite extrapolation is involved. This paragraph together with the explicit finite coefficient list is the certificate for polynomial positivity.

For any t>0, the sum is strictly positive. Since t!=1 for x>0 in either domain, P(t)>0. Hence (U-F)' >0 throughout the relevant connected interval. Both U and F tend to zero at x=0, so U-F>0 everywhere in that interval. This proves (A) and (H) on their full printed scopes.

## Strongest objection and eligibility disposition

The source's Theorem 2, p88, already uses exactly this architecture for 7x/[2+5(1+x²)^(7/15)]: differentiation; v=(1+x²)^(1/15); a sparse polynomial; factor (v-1)^3 times a polynomial with positive coefficients; integrate the strict sign from zero. Theorem 5, pp93–94, applies the negative-sign substitution to arctanh with the same positive factor. Our argument changes the approximation parameters, clears the 109th root and checks a longer finite polynomial. It introduces no new analytic mechanism or substantive source-to-classical bridge. This is an explicit complete source-method adaptation, rather than an exclusion based merely on shortness. Recommend ROUTINE-ADAPTATION EXCLUSION, credit zero. No claim of an earlier public exact proof is made, and no independent eligibility clearance is asserted. No Lean or manuscript investment is justified.
