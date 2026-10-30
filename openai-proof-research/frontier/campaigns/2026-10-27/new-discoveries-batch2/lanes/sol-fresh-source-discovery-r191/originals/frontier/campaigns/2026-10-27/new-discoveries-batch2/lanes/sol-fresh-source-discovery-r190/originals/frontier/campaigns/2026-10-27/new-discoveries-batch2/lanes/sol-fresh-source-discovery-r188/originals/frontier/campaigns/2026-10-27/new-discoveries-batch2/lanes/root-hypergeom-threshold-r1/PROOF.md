# Provisional full zero-balanced Gauss threshold classification

EXCLUDED REDISCOVERY. Credit0. The exact full classification and stronger finite
comparison are already public in trureturing at f8ffe9ed02e01601ed0b43a400ebc1c09cdc6ada.
See ROOT-DECISION.md. The own ordinary argument is preserved below, with no
Lean, paper or discovery claim. One combined family, already resolved.

## Source and exact claim

Qiu-Ma-Xiang, arXiv2408.15723v1 (28 August2024), Conjecture6.2, with
definitions(1.6)-(1.12). The actual v1 PDF is saved; source PDF still needs
visual review in the initial draft; root subsequently rendered and visually read
the entire actual PDFpage22 and definitions on pages2-3. The arXiv version page
lists v1 only. MathDB364530 is the
parameter-range question; MathDB364529's original unrestricted Baricz conjecture
is already refuted in this very source and is excluded, not a new outcome.

Write D_b(r)=2F1(a,b;a+b;r), N_b(r)=2F1(a,b;a+b+1;r), and f_b=N_b/D_b,
where a,b>0 and 0<r<1. The original quotient in(1.6) is f_b/(1-r), so
its b-derivative has the same sign as that of f_b.

Proposed theorem:

1. For each a,b>0, (partial_b f_b(r)<0 for EVERY r in(0,1)) iff
   b^2 <= a(a+1). Equality belongs to the negative-derivative range.
2. More generally, for 0<b1<b2, (f_b1(r)>f_b2(r) for EVERY r in(0,1)) iff
   b1*b2 <= a(a+1).
3. Specializing b1=1-a and b2=3/2-a gives the source's second threshold
   exactly a>=3/7 for 0<a<1.

All statements are ONE classification outcome, if eligible. The source already
proves the necessity via the first Taylor coefficient; that part is uncredited.

## 1. Riccati identities

Fix a,b>0 and put c=a+b, d=ab/c. Let h=1/f=D/N. All involved hypergeometric
series have positive coefficients and are real analytic on[0,1), with positive
denominators; parameter derivatives are locally justified by uniform convergence.
The hypergeometric equation and Euler's transformation give

    N = c(1-r)D'/(ab),
    r f' = c(1-f) - d*r*f^2/(1-r).

Consequently, after t=-log(1-r), T=e^t-1, H(t)=h(1-e^-t), w(t)=H'(t),

    w = d - c*H*(H-1)/T,                           (R)
    T*w' = (d-w)*(T+1) - c*(2H-1)*w.             (R1)

Here and below primes on H,w denote t derivatives. In particular c>0,d>0,
and 4d<=c by (a-b)^2>=0.

The initial data, computed from the first two hypergeometric coefficients, are

    H(0)=1,
    w(0)=ab/[c(c+1)] = d/(c+1) < 1/4,
    w'(0)=ab*(a^2+a+b^2+b)/[c(c+1)^2(c+2)] > 0.  (I)

For completeness, the coefficients of h(r) are

    h1=ab/[c(c+1)],
    h2=h1^2 + ab*(a^2+a+b^2+b)/[c^2(c+1)(c+2)],

and w'(0)=2h2-h1. These are exact identities, not numerical evidence.

## 2. Global strict convexity of the transformed reciprocal

First w(t)>0 for t>=0. If w first reached0 at t>0 after its initially positive
values, (R1) would give w'=d(T+1)/T>0 there, contradicting the nonpositive
derivative at a first zero from above. Hence H(t)>1 for t>0, and (R) gives
w(t)<d there.

Next z=H-w-1/2 is strictly positive. At0, z=1/2-w(0)>0. At a putative first
zero, H=w+1/2>1, so w>1/2, d-w>0, and by(R)

    T = c*(w^2-1/4)/(d-w).

At such a point, (R1) simplifies exactly to

    w' = (d-w)*(d-w-c*(w^2+1/4)) / [c*(w^2-1/4)] < 0,

because d<=c/4 and w>0. Thus z'=w-w'>0, again impossible at a first zero
from above. This proves z>0 globally; the displayed algebra is only used at
a hypothetical boundary, where every denominator is strictly positive.

Finally w'>0 globally. It is positive near0 by(I). At a first zero of w',
differentiating(R1), using T'=T+1 and w'=0, gives

    T*w'' = c*w*(2H-1-2w) = 2c*w*z > 0.

But the derivative of w' at a first zero from above must be nonpositive.
Contradiction. Therefore

    (1-r)*h'(r)=w(-log(1-r)) > w(0)=d/(c+1)       (B)

for every r in(0,1). All first-zero arguments take place on a compact interval
between a sufficiently small positive initial point and any alleged failure;
analyticity supplies continuity and differentiability. No asymptotic assumption
at r=1 is used.

## 3. Full b-derivative classification

Let J=partial_b f_b at fixed a,r. Differentiate the Riccati equation, using
partial_b c=1, partial_b d=a^2/c^2. The resulting linear equation is

    r J' + [c+2d*r*f/(1-r)]J
      = r*f^2/[c*(1-r)] * [a(b-a)/c - w].        (P)

The initial value is J(0)=0. Moreover

    w(0)-a(b-a)/c = a*[a(a+1)-b^2]/[c(c+1)].

If b^2<=a(a+1), (B) makes the right side of(P) strictly negative for every
r>0. Multiplication by the positive integrating factor

    mu(r)=r^c * exp(integral_0^r 2d*f(s)/(1-s) ds)

gives (mu J)'<0. Since mu J tends to0 at0, J<0 throughout(0,1).
All integrals are proper locally up to r<1; mu~r^c at0, and J is bounded there.

If b^2>a(a+1), then

    J(r)= -a*[a(a+1)-b^2]/[c^2(c+1)^2] * r + O(r^2) > 0

for sufficiently small positive r. This proves the iff statement, including
the equality case without an unproved strict-limit argument.

## 4. Full finite-comparison classification

Let c_i=a+b_i, d_i=ab_i/c_i, delta=b2-b1>0, f_i=f_bi, W=f1-f2.
Subtract the two Riccati equations and use the equation for f2. Exactly,

    r W' + [c1+d1*r*(f1+f2)/(1-r)] W
      = delta*r*f2^2/[c2*(1-r)] * [w2-d2+a^2/c1]. (C)

The required initial bound is

    w2(0)-d2+a^2/c1
      = a*[a(a+1)-b1*b2]/[c1*(c2+1)].

When b1*b2<=a(a+1), (B) makes the right side of(C) strictly positive.
Use the integrating factor

    nu(r)=r^c1 * exp(integral_0^r d1*(f1(s)+f2(s))/(1-s) ds).

Since W(0)=0, nu W tends to0 at0; (nu W)'>0 proves W>0 on(0,1).
If b1*b2>a(a+1), the first Taylor coefficient is

    W'(0)=a*(b2-b1)*[a(a+1)-b1*b2]/[c1*c2*(c1+1)*(c2+1)] < 0,

so the uniform comparison fails near0. Finally

    a(a+1)-(1-a)*(3/2-a) = (7a-3)/2,

giving a>=3/7 exactly. This completes the proposed ordinary proof of both
clauses of source Conjecture6.2, in a stronger finite-comparison form.

## 5. Prior-art and scope cautions

No discovery claim yet. Derbazi2607.02511v1, Section3.4/Theorem3.6, explicitly
re-proves only the already known LOCAL failure for b>sqrt(a(a+1)), with
attribution to Qiu-Ma-Xiang; this does not state the sufficiency proved above.
Actual theorem and surrounding proof read. Its general sign-rule theorems
still need a complete subsumption comparison, not dismissal from an abstract.

Han-Cai-Huang, AIMS Math7(4)(2022)4974-4991, DOI10.3934/math.2022277, is a
close convexity lead currently being read. It studies (R(a,b)-log(1-r))/D(r),
which differs from D(r)/N(r), but a genuine corollary route must be tested.
The new content may be routine if a known theorem already gives (B) with the
necessary strictness for all a,b. Independent substantive review is mandatory.

MathDB353557, a different candidate screened in this turn, is ALREADY proved
by Kia Keng Giam, SPL236(2026)110790, DOI10.1016/j.spl.2026.110790,
Theorem1.1 (actual statement/definitions supplied by publisher's indexed primary
body; direct journal request403). Its variance/maximum-exponential representation
is also already Doumas2603.11129. No credit, no Lean investment for that target.

The decisive registry screen subsequently located the exact public proof,
including the literal source objects, both clauses and stronger finite comparison.
No further formalization or acceptance work is planned for this settled family.
Nothing here is a formal certificate. No proof of the stronger auxiliary
transformed-reciprocal curvature is being nominated as a separate outcome.
