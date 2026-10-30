# Complete-monotonicity proof candidate for MathDB370772

2026-10-28. Credit0. No full Lean endpoint, independent review or paper.
This is an ordinary proof candidate, not a demonstrated literature novelty.
Primary target: Chorfi–Et-tahri–Maniar–Yamamoto, arXiv2510.03600v1,
Section5 Conjecture3, Eq5.2. Latest arXiv history checked: v1 only.
Journal DOI10.1016/j.cnsns.2026.109758 exists; actual published conjecture
body has NOT yet been compared. Search summaries/open labels are not gates.

Write E_(a,b)(z)=sum_(n>=0) z^n/Gamma(an+b), E_a=E_(a,1).
The source asks whether, for 0<a<=1/2,

    f_a(t)=E_(2a,1)(-t)^2+t E_(2a,1+a)(-t)^2

is completely monotone (or at least log-convex) for t>0. We propose the
stronger complete-monotonicity conclusion exactly on the full asked range.
The even/odd decomposition of the literal series gives

    f_a(t)=|E_a(i sqrt(t))|^2.                         (1)

All terms at negative real argument are real. The source's other zero-free
conjectures and PDE consequences are not part of this candidate.

## 1. Positive angular identity (generic classical ingredients)

For v,w>0 let S=v+w and theta0=arctan(sqrt(w/v)). Define

    R(theta)^2=min(v/cos(theta)^2,w/sin(theta)^2),
    L(v,w,theta)=S-R(theta)^2,  0<theta<pi/2.

Use the first expression on 0<=theta<=theta0 and the second on
 theta0<=theta<=pi/2, so there are no endpoint divisions by zero.
Then R^2<=S and L>=0: cos^2>=v/S or sin^2>=w/S necessarily, since their
sum is one. Equality only at theta0. Let erfi(x)=2/sqrt(pi)*integral_0^x exp(u^2)du.
For t>=0, polar coordinates in the rectangle [0,sqrt(v)]x[0,sqrt(w)] give

    K(v,w,t)=exp(-St)[1+erfi(sqrt(vt))*erfi(sqrt(wt))]
            =(2/pi) integral_0^(pi/2) exp(-t L(v,w,theta)) dtheta.    (2)

For t>0, expand the product into the rectangle integral:

    exp(-St) erfi(sqrt(vt)) erfi(sqrt(wt))
     =(4t/pi) integral_rectangle exp[-t(S-u^2-z^2)] du dz
     =(4t/pi) integral_theta integral_0^R r exp[-t(S-r^2)] dr dtheta
     =(2/pi) integral_theta [exp(-t(S-R^2))-exp(-tS)] dtheta.

The last exp(-tS) term cancels exactly against the first term of K.
At t=0 both sides equal1 by continuity. Thus (2) is a positive probability
mixture of exponentials for every pair of scales, including unequal ones.
This identity, not numerical differentiation, supplies the sign mechanism.

The half-normal H=|N(0,2)| has characteristic function

    E exp(i z H)=exp(-z^2)[1+i erfi(z)]=E_(1/2)(i z).    (3)

It follows either by completing the square/elementary ODE or by the
half-normal moments E H^n=Gamma(n+1)/Gamma(n/2+1).
For two independent half-normals and scale parameters v,w,

    Re E[exp(i sqrt(t)(sqrt(v)H1-sqrt(w)H2))]=K(v,w,t).

## 2. Finite mixtures at every real index (no stable-law theorem)

Put beta=2a in (0,1]. For each integer N>=1 take independent variables
Y_1,...,Y_N, where Y_k has mass beta at1 and, with mass1-beta, has
Beta(k,1) density k*y^(k-1) on (0,1). This is an explicit finite product
of probability measures, and every variable is positive almost surely.
Set

    V_N=N^(1-beta) product_(k=1)^N Y_k.

For every real q>=0, direct elementary integration gives

    E V_N^q = R_N(q)
      :=N^((1-beta)q) product_(k=1)^N (k+beta*q)/(k+q).              (4)

The classical Euler limit for Gamma yields

    lim_N R_N(q)=Gamma(1+q)/Gamma(1+beta*q).                        (5)

Moreover R_N(q) is nondecreasing in N. To see this, put d=(1-beta)q>=0.
Then

    R_(N+1)(q)/R_N(q)
       =(1+1/N)^d * (N+1+beta*q)/(N+1+q).

Since exp(u)>=1+u and log(1+1/N)>=1/(N+1),

    (1+1/N)^d >= 1+d/(N+1).

Multiplication by the last ratio gives a number at least1, because

    (1+d/(N+1))*(N+1+beta*q) - (N+1+q)
       =d*beta*q/(N+1)>=0.

Thus the finite positive moments satisfy the exact upper bound

    0<R_N(q)<=Gamma(1+q)/Gamma(1+beta*q).                           (6)

For beta=1 every Y_k=1 and V_N=1; all formulas remain true. Let H be
an independent half-normal |N(0,2)| and X_N=sqrt(V_N)*H. Its moments are

    E X_N^n/n! = R_N(n/2)/Gamma(1+n/2)
                 <=1/Gamma(1+a*n),                               (7)

and tend to the last expression. The Mittag-Leffler series converges
absolutely for every complex argument, by the classical Stirling estimate.
Tonelli applied to positive exponential series and (7) shows that
E exp(r X_N)<=E_a(r)<infinity for every r>=0. Therefore, for complex z,

    M_N(z):=E exp(z X_N)
       =sum_(n>=0) z^n R_N(n/2)/Gamma(1+n/2)
       ->sum_(n>=0) z^n/Gamma(1+a*n)=E_a(z).                       (8)

The limit is justified by the summable majorant E_a(|z|), and is locally
uniform in z. This constructs the required approximation at every real a
without assuming a stable distribution, rational Gamma multiplication,
a tightness theorem or continuity in the index. The earlier rational
beta/gamma construction is preserved separately as an independent route.

## 3. Positive Laplace mixtures for the approximants

Take V_N,W_N independent with the same law, and independent half-normals.
Multiplication of expectations in (8), complex conjugation and (3) give

    F_N(t):=|M_N(i sqrt(t))|^2
      =E_(V_N,W_N) K(V_N,W_N,t)
      =E_(V_N,W_N)[(2/pi) integral_0^(pi/2) exp(-t L(V_N,W_N,theta)) dtheta]. (9)

Every integrand is nonnegative, at most1, with L>=0. The imaginary part of
the product cancels by symmetry of the identically distributed scales;
its real part is precisely the kernel K. No uncontrolled integration of
complex-growing expressions occurs: each characteristic function is
bounded by1, and the final kernel is positive bounded.

For any integer k>=0, t>=0 and h>0, the finite binomial expansion gives

    (-1)^k Delta_h^k F_N(t)
       =E_(V_N,W_N,theta)[exp(-tL)(1-exp(-hL))^k]>=0.               (10)

In particular every F_N is a positive Laplace mixture. No differentiation
under an unbounded-scale integral is needed for the conclusion.

## 4. Passage to the actual source function

For every t>=0, (8) yields F_N(t)->|E_a(i sqrt(t))|^2=f_a(t). Pass N to
infinity in the finite sum in (10). Thus (-1)^k Delta_h^k f_a(t)>=0 for
all k,t,h. The even/odd series identity (1) expresses f_a as

    E_(2a,1)(-t)^2+t E_(2a,1+a)(-t)^2,

which is an entire function of t with real coefficients. In particular it
is smooth on the real positive axis. Dividing by h^k and letting h down
to0 gives Delta_h^k f_a(t)/h^k -> f_a^(k)(t), so

    (-1)^k f_a^(k)(t)>=0 for every k>=0 and t>0.

This proves the full complete-monotonicity option in Conjecture3 for every
real 0<a<=1/2. The finite-difference passage requires no unproved weak
convergence, no closure theorem for measures and no uniform high moments.

## Gates and strongest possible objections

- The proof uses only classical gamma/beta moments, Gaussian integrals,
  polar coordinates, Euler Gamma limits and finite differences. Whether
  the particular half-normal cross-scale identity is already published, or
  the whole statement is an immediate existing mixture theorem, remains an
  explicit prior-art/substantive gate. A generic tool is not claimed new.
- Two distinct distributions are called Mittag-Leffler: the law with mgf
  E_a(z) used here is the M-Wright/inverse-stable law with exponentially
  bounded tails, NOT the heavy-tailed law with Laplace1/(1+t^a). Confusing
  them would invalidate the argument. Construction(4)-(7) removes ambiguity.
- No independent reviewer has yet scrutinized the angular identity or the
  finite-product approximation. Full literal Lean needs actual series
  convergence, finite mixture measures, Euler Gamma limits, complex moments,
  angular identity, finite differences and real analyticity; there is no
  existing MittageLeffler/Wright/stable-law definition in the pinned Mathlib.
  An abstract Laplace-mixture theorem with (8) assumed is not full credit.
- Source journal body, latest followups/citers and public formal registries
  have not yet been sufficiently screened. Direct publisher requests blocked;
  no journal-scope or novelty clearance follows from matching metadata.
- Initial other probes (Deb–Sokal Hurwitz/Stirling and Sobolewski–Ulas Hankel
  monotonicity) produced no mathematical result. Their source HTML is cached
  only to preserve the screening trail. No credit or finite-check promotion.

No source question is accepted, posted, or claimed newly resolved yet.
