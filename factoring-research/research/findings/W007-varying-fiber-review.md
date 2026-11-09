# W007 varying-fiber review: the construction criterion survives; the four displayed PTE families do not pass it

2026-10-08. T3 child validator, exclusive varying-coefficient scope.
Disposition: **accept the conditional algebra, reject the four displayed
Choudhry families as suppliers, retain the rational acquisition gap.**
Verified new factoring complexity improvement: **NONE**.

The additive-triple construction is correct, with the restrictions below.
The symmetric size-eight composition test is also correct. A further explicit
translation gives the requested recurrence coefficients from any qualifying
pair; this does not automatically retain the particular fixed quartic P_2.

The bounded source check has a sharper negative conclusion than merely
"the extra condition is not an identity": **none of the four one-parameter
families displayed in Choudhry's paper has a rational specialization satisfying
the composition condition.** The obstruction is an exact polynomial identity
modulo 7 for each of the three possible pairings in each family. It rules out
all rational parameter heights, and does not arise from a parameter sweep.

The second paper supplies relevant finite-field constructions, not the missing
rational family. Its Chebyshev size-eight shape satisfies the composition
identity, but no fiber of T_8 over Q splits entirely into rational roots.
This is proved below, independently of the paper's local assertions.

No compatible rational size-sixteen construction has been obtained here.
This is not a nonexistence theorem for other PTE families, the additive-triple
surface, or a scalable circuit over composite residue rings.

## 1. Scope, source provenance, and work performed

Read AGENTS.md, RESEARCH_TEAM.md, RESEARCH_LOOP.md, README.md,
docs/SPECIFICATION.md and research/STATE.md, and the complete parent note
research/findings/W007-varying-split-fibers.md. Their byte snapshots and hashes
are in [the input manifest](W007-varying-fiber-review-snapshots/manifest.json).
The parent note is preserved. No task-A group, branch, genus, constant-field,
or adaptive-law audit was performed or assumed complete.

The primary sources checked were:

1. Ajai Choudhry, [Ideal solutions of the Tarry-Escott Problem of degree seven,
   arXiv:2207.12726v1](https://arxiv.org/html/2207.12726v1).
   Read the entire mathematical text: introduction; section 2, equations
   (2.1)–(2.13); all three subsequent unnumbered families; concluding paragraph;
   references. Its four explicit families are the precise candidates audited
   here. No cited predecessor paper was fetched. The displayed moment notation
   in (2.2) has y_i^4 on the right even when r varies; the intended r=2,4,6
   identities for the final families were checked independently as polynomial
   identities, so this rendering/text issue is not imported as an assumption.

2. Coppersmith, Mossinghoff, Scheinerman and VanderKam,
   [Ideal Solutions in the Prouhet–Tarry–Escott problem,
   arXiv:2304.11254v1](https://arxiv.org/html/2304.11254v1).
   Read abstract and section 1; section 2's opening definitions and (8)–(9);
   section 3 in full, including the Chebyshev/Dickson identities, Lemmas 3.1–3.2
   and Theorems 3.1–3.2; section 4's introduction and section 4.2 in full.
   Portions of sections 2.1–2.2 were also returned by the browser and skimmed.
   No proof or search result in those latter sections, section 4.1, or
   sections 5–6 is independently certified here. The source describes finite
   searches and local constructions, and points elsewhere for size-eight
   rational families; it does not provide the missing rational specialization
   in the passages checked. No paper-wide absence or priority claim is made.

Both official HTML files and text extractions are saved under the owned
snapshot prefix. The HTML for 2304.11254v1 displays a generated internal date
of August 24, 2026 while the arXiv record says submitted April 21, 2023;
the URL and archived bytes identify the exact text used, without inferring
a new version from that internal date.

Only symbolic coefficient arithmetic was executed: expansion of the four
published families' even moments; construction of twelve pairing polynomials;
Euclidean polynomial gcds; and finite-field polynomial identities. The bounded
local calculation used the fixed primes 7,17,23,31 for those twelve equations.
Only 7 is needed for the conclusion; all the other results are retained.
There were no rational parameter trials, candidate evaluations, height sweeps,
factoring experiments, solver/Lean edits, dependency installations, shared-file
edits, delegation, commits, or publication. No factoring test suite was run.
The [verification log](W007-varying-fiber-review-snapshots/certificate-verification.txt)
records a separate coefficientwise recheck: all 32 root formulas were parsed
directly from archived source TeX and matched against the calculation inputs;
all twelve full Bezout certificates were verified by multiplication, rather
than relying only on the gcd routine that produced them.

## 2. Exact split-value set for the fixed quartic

Write F(X)=P_2(X). Then

    F(X) = (X^2-X-1)^2-1.

For s^2=1+t,

    F(X)-t = (X^2-X-1-s)(X^2-X-1+s).

Thus a simple rational split fiber has roots

    (1+A)/2, (1-A)/2, (1+B)/2, (1-B)/2,

where

    A^2=5+4s,  B^2=5-4s,
    A^2+B^2=10,  s=(A^2-B^2)/8,
    t=s^2-1.

Conversely, if F-t splits simply over Q, evaluating X^2-X-1 at one rational
root gives rational s, and the two quadratic discriminants give rational A,B.
The simplicity conditions are A*B*(A^2-B^2) != 0. Equivalently the excluded
critical values are t=-1 and t=9/16. In fact neither exceptional case occurs
at a rational point of A^2+B^2=10: it would require 5 or 10 to be a rational
square. Retaining the exclusions is useful over other fields.

The parent's parametrization checks exactly:

    A=(1-u^2-6u)/(1+u^2),
    B=(3-3u^2+2u)/(1+u^2).

It covers the rational circle after adjoining u=infinity, which supplies
(-1,-3). Every nonzero split value has a finite parameter, since that omitted
point gives t=0. For subsequent algebra one can use the particularly explicit
formula

    tau(u) = f(u)/d(u),
    f(u) = -u(3u-1)(u+3)(u-1)(u+1)(2u+1)(u-2),
    d(u) = (1+u^2)^4.

Indeed A^2-B^2=-8(u^2-4u-1)(u^2+u-1)/(1+u^2)^2; subtracting 1 from its squared
eighth gives this factorization. Over Q, d(u) never vanishes. The finite
zero-value exceptions are precisely

    u in {0, 1/3, -3, 1, -1, -1/2, 2}.

Also S is contained in the real interval (-1,9/16); this bound alone gives
neither an additive triple nor its nonexistence.

## 3. Additive triples: sufficiency and necessity

Let t_1,t_2,t_3 be rational split values, with

    t_1+t_2=t_3,
    t_1*t_2*t_3*(t_1-t_2) != 0.

The four values 0,t_1,t_2,t_3 are then pairwise distinct. The identities are

    P_3 = F(F-t_3),
    P_3+t_1*t_2 = (F-t_1)(F-t_2),
    P_4 = F(F-t_1)(F-t_2)(F-t_3).

Fibers of the same function at distinct values have no common root. Since
each quartic is simple and splits over Q, P_4 has exactly sixteen distinct
rational roots. Its recurrence coefficients are exactly

    a_0=1,  a_1=2,  a_2=t_3,  a_3=-t_1*t_2.

There is also a direct necessity statement: suppose the recurrence with this
fixed F has sixteen distinct rational roots. Then a_2 and a_3 are nonzero,
F-a_2 splits simply, and the quadratic

    V^2-a_2*V-a_3

has two distinct rational roots t_1,t_2. To see their rationality without
assuming it, take a rational root x of P_3-a_3 and put t_1=F(x); the other
root is t_2=a_2-t_1. Every root of F-t_i is a root of the fully split
P_3-a_3, so both quartics split simply. Neither t_i is zero or a_2 because
a_3 != 0. Vieta now gives t_1+t_2=a_2 and -t_1*t_2=a_3. Thus the condition
is necessary even without separately assuming that the intermediate fibers
have been supplied as rational data.

This is a construction conditional on obtaining a point, not a procedure
that obtains one. In explicit circle parameters the remaining equation is

    f(u_1)d(u_2)d(u_3) + f(u_2)d(u_1)d(u_3)
      - f(u_3)d(u_1)d(u_2) = 0,                         (A)

subject to f(u_1)f(u_2)f(u_3) != 0 and

    f(u_1)d(u_2)-f(u_2)d(u_1) != 0.

These conditions are exhaustive for the nontrivial fixed-F construction over
Q. No rational point on this permitted part of (A) is asserted here.

## 4. Newton equivalence and the precise composition test

For a monic polynomial with elementary symmetric coefficients e_j and root
power sums p_j, Newton's identity for 1<=j<=d is

    p_j-e_1*p_(j-1)+e_2*p_(j-2)-...+(-1)^j*j*e_j=0.

Over Q it recursively equates p_1,...,p_(d-1) with e_1,...,e_(d-1).
Thus two monic degree-d root polynomials differ by a constant exactly when
those power sums agree. A nonzero constant ensures the two root multisets
are disjoint; it does not ensure simplicity within either multiset.
Clearing a common root denominator preserves these equalities. This proves
the required ideal-PTE equivalence directly, without importing a theorem.

For a symmetric size-eight ideal pair, translate its common center to zero
and write its half-roots as x_1,...,x_4 and y_1,...,y_4. Half-roots need not
be positive; their signs are irrelevant. Let

    Q_x(Y)=product_i(Y-x_i^2)=Y^4+B*Y^3+C*Y^2+D*Y+E_x,
    Q_y(Y)=product_i(Y-y_i^2)=Y^4+B*Y^3+C*Y^2+D*Y+E_y.

The shared B,C,D follow from the moment identities. On writing

    (Y^2+u*Y+v)^2+w*(Y^2+u*Y+v)+z,

one obtains B=2u, C=u^2+2v+w, and D=u(2v+w). Consequently the necessary
and sufficient condition is

    D=(B/2)*(C-B^2/4).                                 (C)

For sufficiency choose v=0, u=B/2, w=C-B^2/4, z=E. No square-root extraction
or point oracle is hidden in this coefficient identity.

Put s_i=x_i^2 and let e_j be their elementary symmetric functions. Then (C)
is also equivalent to

    e_1^3-4*e_1*e_2+8*e_3
      =(s_1+s_2-s_3-s_4)(s_1+s_3-s_2-s_4)
        *(s_1+s_4-s_2-s_3)=0.                         (P)

This gives all three pairings, not just a chosen one. Alternatively, translating
Y by -B/4 makes Q even exactly when (C) holds; its split roots then pair by
reflection with common sum H=-B/2. The y half-roots also pair with this same
H, since B,C,D are shared. The parent’s equal-circle-sum criterion is correct
provided both sides use the same H. The equal fourth powers then force equal
sixth powers by the two displayed pair identities in the parent note.

### Explicit conversion to four stages, including all rational degeneracies

Suppose a rational symmetric ideal pair satisfies (C). Set

    H=-B/2,  w=C-H^2,
    R(Z)=Z^4-H*Z^2,
    F_x(Z)=Q_x(Z^2)=R(Z)^2+w*R(Z)+E_x,
    F_y(Z)=F_x(Z)+E_y-E_x.

Choose any supplied half-root r=x_i, put k=r^4-H*r^2, and change variable
Z=X+r. The exact recurrence coefficients are

    a_0=-2r,
    a_1=H-2r^2,
    a_2=-(2k+w),
    a_3=E_x-E_y.                                     (R)

In fact

    P_1=X(X+2r),
    P_2=P_1(P_1-a_1)=R(X+r)-k,
    P_3=P_2(P_2-a_2)=F_x(X+r),
    P_4=P_3(P_3-a_3)=F_x(X+r)*F_y(X+r).

The constant term in P_3 vanishes because k^2+w*k+E_x=F_x(r)=0.
This supplies actual coefficients rather than merely an existence claim.
Conversely, the first three quadratic stages, after centering the first
quadratic, yield a quartic in Z^2 that satisfies (C). Thus this is an exact
criterion for using the given symmetric pair as the two degree-eight
factors of this four-stage recurrence, up to rational input translation.

Necessary and sufficient rational simplicity/nontriviality restrictions are

    all x_i,y_i are defined and nonzero;
    x_i^2 != x_j^2 and y_i^2 != y_j^2 for i != j;
    E_x != E_y.

The last restriction prevents every cross-set collision by the constant
difference. These conditions also force a_0,a_1,a_2,a_3 != 0. All parameter
denominators must be nonzero; a rational scaling, if used, must be nonzero.
There are no other rational degeneracies once the PTE equalities and (C)
hold. Formula (R) itself uses only rational additions and multiplications
apart from the displayed division by 2 and whatever denominators came with
the supplied pair.

This conversion **does not in general keep F=X(X-1)(X-2)(X+1)**. The selected
first quartic has centered roots {+r,-r,+s,-s}, where r^2+s^2=H. It can be
carried to the fixed F by a rational affine input change and monic output
normalization exactly when its two nonzero magnitudes have ratio 3, i.e.
s^2=9r^2 or r^2=9s^2. One may select another pairing/factor first, but that
ratio requirement still has to be met for the selected quartic. A general
compatible PTE pair solves the varying-all-earlier-coefficients problem,
not automatically equation (A) for the fixed F.

## 5. Choudhry's four displayed families: a rational obstruction

Label family 1 by (2.13), and families 2,3,4 by their displayed order after
it. Use the x_i in each display, without sign changes or rescaling. For
j=2,3,4, form the primitive integer polynomial with positive leading
coefficient proportional to

    x_1(t)^2+x_j(t)^2-sum_(i not in {1,j}) x_i(t)^2.

Call this polynomial h_(f,j)(t). Taking its primitive part changes no
characteristic-zero zero. Identity (P) says compatibility is exactly that
at least one of these three polynomials vanishes.

The complete exact x/y coefficients, expanded h polynomials, even-moment
residuals, constant differences and rational polynomial gcds are saved in
[symbolic-family-results.json](W007-varying-fiber-review-snapshots/symbolic-family-results.json).
All twelve even-moment residuals (four families times r=2,4,6) are the zero
polynomial. None of the twelve h polynomials is zero. Their degrees are all
8, and their leading coefficients, in pairing order 12,13,14, are

    family 1:  1,  1,  1
    family 2: 55, 41, 25
    family 3: 29, 19, 13
    family 4:  5,  1,  5.

In particular every leading coefficient is a unit modulo 7. The decisive
additional fact, for every one of the twelve polynomials, is

    gcd_(F_7[t])(h_(f,j)(t), t^7-t)=1.                (7)

Here are compact certificates that can be checked solely by multiplication
and polynomial reduction. Each line gives f,j, then the coefficient lists
of R=h mod (t^7-t) and U, in **ascending powers** of t, in F_7. In each case
U*R is congruent to 1 modulo t^7-t:

    1,2  R=[4,1,5,2,4,0,3]  U=[2,2,1,3,3,4,2]
    1,3  R=[4,6,1]          U=[2,2,4,4,0,6,5]
    1,4  R=[5,6,3,5,1,0,3]  U=[3,5,2,0,1]
    2,2  R=[5,1,5,5,0,5,5]  U=[3,6,6,2,0,3,4]
    2,3  R=[5,6,3,1,4,4]    U=[3,3,2,5,6,4,2]
    2,4  R=[5,4,2,5,6,6,6]  U=[3,6,0,3,5,0,3]
    3,2  R=[3,2,5,5,1,3]    U=[5,0,2,5,2,4,6]
    3,3  R=[1,4,2,6,0,4,6]  U=[1,0,0,6,5,1,5]
    3,4  R=[6,2,1,6,2,1,6]  U=[6,3,5,2,3,5,2]
    4,2  R=[4,4,0,0,6,4,6]  U=[2,2,4,5,5,2,6]
    4,3  R=[6,4,4,4,2,5,2]  U=[6,3,5,3,6,0,4]
    4,4  R=[5,3,4,3,1,1,5]  U=[3,3,6,3,2,1,4].

Full Bezout identities U*h+V*(t^7-t)=1 modulo 7 are saved in
[symbolic-mod7-certificates.json](W007-varying-fiber-review-snapshots/symbolic-mod7-certificates.json).
This is a proof certificate, not a table of evaluated parameters.

For completeness, suppose a/b in lowest terms were a rational zero of h.
If 7 does not divide b, its reduction gives a zero of h in F_7, contradicting
(7). If 7 divides b, homogenizing the degree-eight equation gives, modulo 7,
leading_coefficient*a^8=0, again impossible. The leading coefficients also
exclude the homogeneous point at infinity, so homogenizing the published
quartics does not supply a compatible limiting specialization there.
Therefore all four displayed families fail the composition condition at
every rational parameter, even before simplicity and nontriviality filters.
Common affine transformations cannot repair this: recentering removes the
translation, and a nonzero scaling multiplies every squared-pair difference
by the same nonzero square.

The source's broader elliptic construction is not exhausted by these four
families. No claim is made about its other rational points, algebraic
parameter specializations with separate descent, or other published families.
The extra composition equation remains indispensable for such alternatives.

## 6. The local Chebyshev shape fits, but is not a rational split family

Section 3 of the second source discusses fibers of Chebyshev polynomials
over suitable F_p. For size eight its actual monic shape is

    (T_8(Z)-c)/128
      = Z^8-2Z^6+(5/4)Z^4-(1/4)Z^2+(1-c)/128
      = R(Z)^2+(1/4)R(Z)+(1-c)/128,
    R(Z)=Z^4-Z^2.

Thus B=-2, C=5/4, D=-1/4, H=1, w=1/4 satisfy (C). For any supplied root r
of T_8-c_1 in the relevant field, (R) specializes to the actual circuit

    k=r^4-r^2,
    a_0=-2r,
    a_1=1-2r^2,
    a_2=-2k-1/4,
    a_3=(c_2-c_1)/128,

whose P_4 is

    (T_8(X+r)-c_1)(T_8(X+r)-c_2)/128^2.

In characteristic different from 2, the restrictions for sixteen distinct
roots are: both fibers split; c_1 != c_2; and c_1,c_2 not in {+1,-1}.
The latter exclude the critical values and hence all within-fiber repeated
roots. These requirements imply that the field has at least sixteen elements.
The only displayed scalar denominators are powers of 2, besides denominators
of supplied parameters. A theorem furnishing split **multisets** that permits
c=+1 or -1 does not by itself meet the distinct-root requirement.

There is an elementary obstruction over Q. Suppose T_8-c split over Q.
From T_8=2*T_4^2-1, a rational root furnishes a rational d with d^2=(c+1)/2,
and both T_4-d and T_4+d must split rationally (with multiplicity allowed).
The roots of T_4-d have the form +/-r,+/-s with rational r,s and

    r^2+s^2=1,  d=1-8r^2*s^2.

The squared roots of T_4+d are then

    1/2+r*s=(r+s)^2/2,
    1/2-r*s=(r-s)^2/2.

For all its roots to be rational, both (r+s)/sqrt(2) and (r-s)/sqrt(2)
must be rational. Since r,s are rational, this forces r+s=r-s=0, contrary
to r^2+s^2=1. Thus **no rational value c has a completely rational split
T_8 fiber**, including the repeated-root cases.

The source's local construction therefore neither supplies a rational
size-eight pair nor a fixed-F additive triple. Locally its split-fiber
conditions, useful parameters and any primitive roots/field extensions used
to construct them still have to be obtained without the unknown input primes.
The Chebyshev evaluator is succinct, but the local acquisition and separation
obligations have not been discharged. No universal all-size result follows.

## 7. Root separation and complete cost obligations

For a fixed successful additive triple there is a particularly short
separation certificate. Direct discriminant calculation gives

    disc(F-t)=16(9-16t)(1+t)^2.

For tau_0=0,tau_1=t_1,tau_2=t_2,tau_3=t_3,

    disc(P_4)
      = product_i [16(9-16tau_i)(1+tau_i)^2]
        * product_(i<j)(tau_i-tau_j)^8.               (D)

This uses Res(F-tau_i,F-tau_j)=(tau_i-tau_j)^4. It avoids expanding sixteen
roots or a huge discriminant integer. At any prime where the coefficient
denominators are units and (D) is nonzero, the already-proved rational
splitting reduces to sixteen distinct local roots. Rational roots of a monic
p-integral polynomial are p-integral, so this statement does not require
enumerating them to reduce them.

Alternatively, for any rational root list rho_i=m_i/D_0 the finite bad-prime
set is contained among divisors of D_0*product_(i<j)(m_i-m_j). This elementary
description proves a finite exception set; it is not free computation of that
large product. Formula (D), or another explicitly supplied short certificate,
is preferable when available. For a general compatible pair one has

    disc(F_x)=2^8*product_i(x_i^2)
                    *product_(i<j)(x_i^2-x_j^2)^4,
    disc(F_x*F_y)=disc(F_x)*disc(F_y)*(E_y-E_x)^16.

Every denominator used by the selected modular circuit must be gcd-tested
before inversion. A proper gcd is an early factor; gcd=N is failure of that
parameter/chart and cannot be reported as a factor. The same distinction
applies when using gcd tests on separation factors. A short alternative chart
may handle a failed denominator, but supplying and executing it costs work.

The evaluator with supplied coefficients uses four recurrence multiplications
at this depth, after paid modular coefficient acquisition. At depth j it uses
O(j) modular operations; this is not a bound for constructing those coefficients.
For an explicit coefficient circuit of length L with actually supplied constants,
one can reduce each gate modulo an n-bit N. Charge O((L+j)M(n)) for modular
arithmetic, plus actual constant reading/reduction, gcd/inversion, control,
storage, parameter generation, rejected charts and restarts. Constants supplied
as expanded b-bit integers cost their actual input/reduction work; constants
generated by a short circuit need not be expanded to their potentially enormous
rational heights. Conversely, the existence of a short circuit does not supply
an algorithm to discover or construct it.

Even a valid degree-sixteen example would supply only fixed local coverage.
For a scalable factoring claim one must still provide all of the following:

- A uniform, paid generator at growing depth, without rational-point,
  useful-fiber, splitting-field or hidden-prime advice.
- A count of distinct useful roots modulo the actual unknown prime factors,
  respecting degree versus field size, bad reductions and failed parameters.
- A lower bound for obtaining a **proper** gcd, including joint behavior at
  different prime factors and full-gcd failures; local root density alone is
  insufficient. No task-A adaptive law is re-audited or upgraded here.
- Complete acquisition, evaluation, gcd recovery, restart and input-width
  costs, and correct handling of repeated-prime inputs and small factors.
- A comparison to an appropriate factoring baseline under the same scope and
  assumptions, rather than comparison to sixteen individually expanded factors.

Neither source check nor these identities establish any of those growing-depth
supply/success bounds. They also establish no general circuit lower bound.

## 8. Next decisive action

Close the proposed use of Choudhry's **four displayed** quartic-parameter
families: their modulo-7 obstruction is complete for rational parameters, so
increasing a rational-height budget there cannot help.

For the parent's fixed-F route, the exact remaining constructive target is
one rational point on (A) outside its explicitly listed exceptional divisors,
obtained by a finite symbolic construction. An explicit rational curve on (A)
avoiding those divisors would be stronger. For a route that varies all earlier
coefficients, require an actual symmetric ideal pair satisfying (C), then
use (R) and its degeneracy conditions; a generic ideal-PTE parametrization
alone is not enough. A follow-up should select one of these two algebraic
targets and a bounded proof/construction method before authorizing further work.

No numerical experiment or broader source hunt is recommended by default.
The finite-stage algebra remains useful as a gate, but the parent's research
objective remains a scalable paid root-cover circuit with a separating factor
law, not merely a size-sixteen polynomial.
