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

## 2. A self-contained rational-index scale mixture

Classical subordination already represents the M-Wright law at a<=1/2
as a mixture of half-normals. To avoid assuming this theorem, here is an
explicit finite beta/gamma construction for rational 2a, followed by limits.

Let beta=2a=p/q with integers 1<=p<q. Take independent random variables

    B_j ~ Beta(j/q,j/p-j/q),  1<=j<=p,
    G_j ~ Gamma(j/q,rate1),  p+1<=j<=q.

Every beta and gamma parameter is strictly positive. Put

    V=(q/p^(p/q)) * (product_j B_j * product_j G_j)^(1/q).            (4)

The beta integral and gamma integral give their moments. Gauss's
multiplication formula, normalized by its value at zero, gives for all s>=0

    E V^s
      =(q/p^(p/q))^s
         [product_(j=1)^q Gamma(j/q+s/q)/Gamma(j/q)]
         /[product_(j=1)^p Gamma(j/p+s/q)/Gamma(j/p)]
      =Gamma(1+s)/Gamma(1+beta*s).                     (5)

For beta=1 instead take V=1 deterministically; (5) remains true.
No unproved infinite-product positivity or stable-density assertion is used.
Let H be independent of V and X=sqrt(V)H. Equations(3),(5) give

    E X^n = Gamma(n+1)/Gamma(1+a*n),  n>=0.             (6)

The defining Mittag-Leffler series converges for every complex argument:
Stirling's gamma estimate gives zero coefficient root limit. In particular,
for r>=0, Tonelli/monotone convergence gives

    E exp(rX)=sum_n r^n E X^n/n! = E_a(r)<infinity.

Consequently the complex exponential can also be integrated termwise,
dominated by exp(|z|X), yielding the genuine identity

    E exp(zX)=E_a(z),  z in C.                         (7)

This is the actual entire function in the source, not a renamed surrogate.

## 3. Complete monotonicity at rational a

Let V,W be independent copies of (4), with independent half-normals.
By(7), multiplication of expectations and symmetry under interchange V,W,

    f_a(t)=E_(V,W) K(V,W,t)
          =E_(V,W) [(2/pi) integral_0^(pi/2) exp(-t L(V,W,theta)) dtheta].  (8)

All angular integrands are nonnegative and bounded by1. This is a Laplace
transform of a probability measure on the nonnegative half-line. In
particular, for every integer k>=0, t>=0 and h>0,

    (-1)^k Delta_h^k f_a(t)
     =E_(V,W,theta)[exp(-tL)(1-exp(-hL))^k]>=0.         (9)

One may also differentiate at t>0: L^k exp(-tL) is uniformly bounded
in L>=0 on a compact positive t interval. Thus(8) directly gives smoothness
and alternating derivatives. The finite-difference version is sufficient
for the final parameter passage and avoids any uniform moment assumption.

## 4. All real 0<a<=1/2

Choose rational a_l in (0,1/2] tending to a. The Mittag-Leffler series,
including their derivatives in t after the even/odd decomposition (1),
converge locally uniformly in t and uniformly for a in a compact positive
interval. For all sufficiently large n their gamma denominators are bounded
below by Gamma(epsilon*n+1), using monotonicity of Gamma above2. This is a
summable entire-series majorant. Hence f_(a_l)(t)->f_a(t) for every t>=0,
and f_a is real analytic in t (indeed its expression in (1) is entire).

Pass to the limit in the finite sum Delta_h^k in(9). For every k,t,h,
(-1)^k Delta_h^k f_a(t)>=0. Divide by h^k and let h down to0. Analyticity
gives h^(-k)Delta_h^k f_a(t)->f_a^(k)(t), proving

    (-1)^k f_a^(k)(t)>=0 for all k>=0 and t>0.

This proves exactly the full complete-monotonicity option in Conjecture3.

## Gates and strongest possible objections

- The proof uses only classical gamma/beta moments, Gaussian integrals,
  polar coordinates, Gauss multiplication and finite differences. Whether
  the particular half-normal cross-scale identity is already published, or
  the whole statement is an immediate existing mixture theorem, remains an
  explicit prior-art/substantive gate. A generic tool is not claimed new.
- Two distinct distributions are called Mittag-Leffler: the law with mgf
  E_a(z) used here is the M-Wright/inverse-stable law with exponentially
  bounded tails, NOT the heavy-tailed law with Laplace1/(1+t^a). Confusing
  them would invalidate the argument. Construction(4)-(7) removes ambiguity.
- No independent reviewer has yet scrutinized(2),(4)-(8). Full literal Lean
  needs actual series convergence, beta/gamma products, complex moments,
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
