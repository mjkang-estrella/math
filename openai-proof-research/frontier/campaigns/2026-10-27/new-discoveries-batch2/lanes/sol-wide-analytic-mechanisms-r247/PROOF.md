# Sublinear stable approximation for the intended binomial question

Provisional ordinary-mathematics proof, requiring independent review and current prior-art/substantive screening. No acceptance or priority claim.

For every integer n>=1 let X_n have law Bin(3n,1/2). There exist 2n numbers p[n,j] in (0,1) such that, for independent Bernoulli variables with these parameters and their sum Y_n,

    W_infinity((2/3) X_n,Y_n)/n -> 0.

This answers the intended existence/o(n) clause of Tang–Tang, 1908.10024v1, Open Problem4.6, PDFp11, under the support {0,...,2n} fixed in Eq(4.6), p10 and the immediately preceding construction on p11. The displayed Problem4.6 says n parameters although its preceding paragraph says 2n. With literally n Bernoulli summands the essential supremum obstruction is >=n, since (2/3)X_n=2n with positive probability and Y_n<=n. We do not label that typographical endpoint observation a discovery. We prove the mathematically substantive intended 2n endpoint above, and do NOT solve O(1), the best lower bound, arbitrary Poisson-binomial parents, or multivariate stable multiplication.

## Explicit construction

Put a=2/3, theta=pi*a. For u in (0,1) set

    r(u)=[sin(theta*u)/sin(theta*(1-u))]^(1/a),
    p(u)=1/(1+r(u)),
    p[n,j]=p((j-1/2)/(2n)),  j=1,...,2n.

The quotient is strictly increasing: its derivative is theta*sin(theta)/sin(theta*(1-u))^2>0. In particular r(0+)=0, r(1-)=infinity. The parameters are positive and below1; p(1-u)=1-p(u), so E Y_n=n exactly. Every Y_n has a real-negative-rooted PGF, the product of its Bernoulli linear factors. No unproved real-rootedness operation is needed.

## Spectral measure identity

For 0<a<1 define a probability measure on (0,infinity) with density

    dmu_a(r)/dr = sin(pi*a)/pi * r^(a-1)/(1+2*r^a*cos(pi*a)+r^(2a)).

The substitution v=r^a gives its distribution function

    [atan((r^a+cos(theta))/sin(theta))-(pi/2-theta)]/theta.

It increases from0 to1. Solving for r gives exactly the r(u) above. For every z>0,

    integral z/(z+r) dmu_a(r) = z^a/(1+z^a).             (1)

Here is a proof rather than an appeal to a named representation theorem. Use the principal branch on C minus the negative real axis for h(w)=w^(a-1)/(1+w^a). There are no poles in that domain, since |arg(w^a)|<pi*a<pi. Cauchy's formula on a keyhole contour gives h(z) as its cut-jump integral: the outer-circle contribution tends to0 because h(w)/(w-z)=O(|w|^-2), and the inner-circle contribution tends to0 because its integral is O(epsilon^a). The upper boundary value has imaginary part

    Im h(-r+i0) = -sin(pi*a)*r^(a-1)/(1+2*r^a*cos(pi*a)+r^(2a)).

The lower value is its conjugate. Thus h(z)=integral (z+r)^-1 dmu_a(r). Multiplication by z proves(1). The estimates apply away from the cut and the boundary integrals converge both at0 and infinity, so the contour limits are justified.

## Matching all finite exponential tilts

Let F_n(t)=n^-1 log E exp(tY_n). Midpoint Riemann sums converge for the continuous function of u obtained by extending p to p(0)=1,p(1)=0. Hence

    F_n(t) -> F(t)=2 integral log((r+e^t)/(r+1)) dmu_a(r).

For fixed real t the integrand and its t derivative are bounded; differentiation under the probability integral is valid. Identity(1) gives

    F'(t)=2 e^(a*t)/(1+e^(a*t)),
    F(t)=(2/a) log((1+e^(a*t))/2).

At a=2/3 this is 3 log((1+e^(2t/3))/2), exactly n^-1 log E exp(t*(2/3)X_n) for EVERY n. The same Riemann-sum argument for derivatives gives F_n'(t)->F'(t). F is strictly convex; F'(R)=(0,2), F'(0)=1. Define

    I(x)=sup_t (tx-F(t)), 0<=x<=2.

On(0,2), the maximizer is uniquely t(x)=(3/2)log(x/(2-x)). Consequently I is strictly decreasing on(0,1), strictly increasing on(1,2), and I(1)=0. It also equals 3[ q log(2q)+(1-q)log(2(1-q)) ], q=x/2.

## Tail estimates, with a proof of the required lower bound

For Z_n=Y_n/n or Z_n=(2/3)X_n/n, we have, for each fixed x in(0,1),

    n^-1 log Pr(Z_n<=x) -> -I(x),                       (2)

and, for each fixed x in(1,2),

    n^-1 log Pr(Z_n>x) -> -I(x).                        (3)

Chernoff's inequality proves the upper bounds using the finite-t cumulant convergence. For completeness, tilt Y_n by exp(tY_n-nF_n(t)), where F'(t)=y in(0,2). The tilted law remains a sum of independent Bernoulli variables; its mean divided by n tends to y, and its variance divided by n^2 is at most1/(2n). Chebyshev therefore puts probability tending to1 in |Y_n/n-y|<delta. Undoing the tilt on this interval gives lower exponential rate at least F(t)-ty-|t|delta. For the left tail take y<x with delta<x-y and let y increase to x and delta decrease to0; for the strict right tail take y>x and decrease y to x. Continuity of t(y),F and I proves(2),(3). For (2/3)X_n the same argument applies to its 3n independent scaled Bernoulli summands, with tilted variance <=n/3 and exact cumulant F. Thus no large-deviation theorem is used as an unproved black box. Both variables also concentrate at1 by their O(n) variances.

## Why these tails give infinity-Wasserstein convergence

We supply the extremal-quantile step; convergence in law or a central limit theorem alone would not suffice. Let A_n=(2/3)X_n/n and B_n=Y_n/n. Both are supported in[0,2]. For their left quantiles Q_A(u),Q_B(u), we claim

    sup_(0<u<1) |Q_A(u)-Q_B(u)| ->0.                   (4)

If false, along a subsequence there are u_n with Q_A(u_n)->x, Q_B(u_n)->y and y-x>=epsilon>0, or the reversed order. Compactness supplies convergent subsequences. Choose x<a<b<y. If the gap contains interior points below1, choose a,b<1. By(2) and I(a)>I(b), eventually Pr(A_n<=a)<Pr(B_n<=b). If the gap instead contains interior points above1, choose a,b>1. By(3) and I(a)<I(b), again Pr(A_n<=a)<Pr(B_n<=b). These choices always cover a positive-length gap; a gap straddling1 contains points on one side as well. But the quantile inequalities give

    u_n <= Pr(A_n<=a),     Pr(B_n<=b)<u_n,

which contradict that strict CDF ordering. The reversed order is identical with A,B exchanged, since they have the same tail rates. This proves(4), including u_n exponentially or superexponentially close to0 or1: a,b stay strictly inside the fixed gap and no endpoint approximation was used.

A common uniform u couples the quantiles with essential sup distance bounded by the supremum in(4). Scaling by n proves the theorem.

## Source-method and credit limits

Tang–Tang Proposition4.5's actual proof uses endpoint mass/entropy to exclude homogeneous binomial approximants; it does not exclude nonuniform empirical odds measures. Its equidistributed-parameter attempt also fails at an endpoint. Ghosh–Liggett–Pemantle1607.03036v1 Section4, Proposition4.2 and Theorem4.3 (PDFpp9–11), prove stable division via residue-polynomial interlacing; the actual induction/proofs were inspected. They explicitly explain failure for2/3 and ask O(1) in Question3 p12. Neither theorem directly gives this asymptotic construction.

The odds measure is classical Stieltjes/complete-Bernstein material. Its use here and the elementary exponential-tilt/quantile bridge could nevertheless be judged a routine complete classical adaptation. This is the strongest substantive objection, not a novelty clearance. No current full public registry heads, exhaustive citers or worldwide priority conclusion are available. Independent adversarial review must check the contour identity, uniform extreme-quantile argument, source scope and classical subsumption before any further investment.
