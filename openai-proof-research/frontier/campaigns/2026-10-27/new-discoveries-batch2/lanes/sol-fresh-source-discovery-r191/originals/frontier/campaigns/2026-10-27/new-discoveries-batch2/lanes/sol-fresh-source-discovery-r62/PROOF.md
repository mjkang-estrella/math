# Complete ordinary refutation, retained UNCOUNTED

This is an independently derived equal-dimension variant of publicly resolved
Kalmykov–Karp Conjectures 1/2. It is **not a discovery nomination**. Public prior
proofs are identified in discovery.md. No Lean work is authorized by this file.

## Literal source and hypotheses

Kalmykov–Karp, Analysis Mathematica 43 (2017), 567–580,
DOI 10.1007/s10476-017-0503-z, equations (9),(10), Theorem 3 and
Conjectures 1/2 on printed pp573–576. Read actual author-hosted typeset body,
`sources/karp2017.pdf`. The latest
arXiv version is v1; its body was also retrieved.

For an integer N>0 let a consist of N copies each of 2 and 3, and b of N
copies each of 1 and 4. Thus p=q=2N and all parameters are positive. Set

    g_N(t) = product Gamma(a_i+t)/product Gamma(b_i+t)
           = ((t+1)/(t+3))^N,
    F_N(t;x) = sum_{n>=0} g_N(t+n) x^n/n!.

The gamma identity follows twice from Gamma(z+1)=z Gamma(z). This is the
literal regularized function (10), without a missing prefactor.
For Conjecture 2 choose empty unshifted blocks and these shifted blocks;
the standing nonempty shifted-numerator condition holds.

Condition (13) holds. Indeed the sorted b-prefix sum is k for k<=N and
4k-3N for N<=k<=2N. The corresponding sorted a-prefix sum is 2k or 3k-N.
In both ranges the former is at most the latter, with equal full sums.
This is exactly a ≺^W b in the source convention (6). The second part of
source Lemma 4, printed p577, implies (13). This is a stated classical
source dependency, not a new theorem. Independent exact coefficient
certificates `hypotheses-35.json` and `hypotheses-100.json` also verify the
entire chain directly: if A_k,B_k are the ascending coefficients of
(z²+5z+6)^N,(z²+5z+4)^N, then B_{k+1}A_k-B_kA_{k+1}>=0 for every
0<=k<2N. These ascending ratios are precisely the source descending
symmetric-function ratios. All denominators are positive.

## A negative literal coefficient

At mu=1 and alpha=beta=1/2 the coefficient of x is

    d_N = 2(35/99)^N - (1/3)^N - (9/25)^N
        = (2*875^N - 825^N - 891^N)/2475^N.

This follows by expanding the two Cauchy terms, retaining both factorials
(which are 1): 2g(3/2)g(5/2)-g(1)g(3)-g(2)^2.
For N=35 the integer numerator is

    -122121556348431894775398027513515665175691905312303735445290928045313496954184124463385941980231507526.

Consequently the coefficient assertion is false with positive noninteger
shifts, mu>=1, alpha<=beta+1, and p=q=70. This is an exact counterexample,
not extrapolation from a finite grid. It does not alone prove a negative
function value, since the constant coefficient is positive.

## Failure of the actual function log-concavity

Take N=100, x=(5/6)^100, s=2^-100, and differentiate in t at t=1.
The terms n=0,1 in F, F', F'' sum respectively to

    2s, (115/3)s, (9323/12)s.

To verify: for z>=1 put u(z)=2/((z+1)(z+3)). Then

    g'=Nu g,
    g''=(N²u²+Nu')g,
    u'=-4(z+2)/((z+1)²(z+3)²).

At z=1, g'/g=25 and g''/g=2425/4. At z=2 these values are
40/3 and 512/3. The choice of x makes both first terms have weight s.
For z>=1, 0<g<=1, 0<u<=1/4, and |u'|<=3/16.
The last bound follows from |u'|=1/(z+1)²-1/(z+3)², decreasing in z.
Therefore |g'|<=25g and |g''|<=(2575/4)g.
These bounds, also locally uniformly in t>=1, justify termwise first and
second differentiation by the exponential majorant.

Write w_n=g(1+n)x^n/n!. Since (log g)''=Nu'<0, the ratio
g(z+1)/g(z) decreases in z. Its value at z=1 is (6/5)^100=1/x.
Thus w_{n+1}/w_n<=1/(n+1). In particular, after w_2 the ratio is at most
1/3. Directly

    w_2/s = (25/27)^100/2.

The exact integer comparison 2000*25^100<27^100 gives

    T := sum_{n>=2} w_n <= (3/2)w_2 < (3/8000)s.

This geometric tail bound controls the entire infinite series, not just
its truncation. Hence

    F>=2s,
    F' <= (115/3 + 75/8000)s,
    F'' >= (9323/12 - 7725/32000)s > 0.

It follows that

    F F''-(F')²
    > [2(9323/12-7725/32000)-(115/3+75/8000)²]s²
    = (76665359/921600)s²
    > 80*4^-100 > 0.

All comparisons here are rational or integer; `compact.py` reproduces
them without numerical special-function evaluation. Thus (log F)''>0
at t=1, and by continuity throughout some interval [1,1+epsilon].
The failure extends to interior t>1; it is not an endpoint correction.
Strict convexity there gives, for sufficiently small h>0,

    F(1+h;x)^2 < F(1;x) F(1+2h;x).

Thus the source function Turanian is negative with mu=1 and alpha=beta=h>0.
Both the coefficient and function conclusions of Conjecture 1 fail;
with empty unshifted blocks the corresponding Conjecture 2 assertions
also fail. No optimal dimension, least N, uniform parameter classification,
or discovery priority is claimed.
