# Proposed C*-algebraic Sendov counterexample by continuous branch obstruction

26 October2026. **Credit0 pending final review and packet acceptance**. Complete
hand argument and136-declaration full strict Lean proof;3-page paper complete.
Independent preliminary source/math/bounded-novelty/eligibility review passes.
The original mathematical body was frozen at3c62435432; only this status prelude
has been updated for the current review candidate.
This is ONE proposed source-conjecture refutation, not separate credits for variants.

## Exact source

Krishna, *C*-algebraic Gauss-Lucas theorem and C*-algebraic Sendov's conjecture*,
Vestnik KRAUNC54(1)(2026),56–63, DOI10.26117/2079-6641-2026-54-1-56-63.
Actual publisher pp59–60 rendered and visually inspected. Published Conjecture3
(p60), originally2203.06916v1 Conj2.5, is MathDB353909: a unital C*-algebra,
all polynomial roots in its C*-unit disc, n−1 critical roots in the disc,
each a positive-coefficient convex combination of the roots; asks for a critical
root within the C*-unit disc around each prescribed root. Published Conjecture4
additionally formulates the fully split derivative variant without convex weights.
The proposed example satisfies BOTH sets of hypotheses, including the stronger
complete derivative factorization and strictly positive continuous weights.

MathDB353908 is the commutative formulation (published Conj2 / preprint2.4),
with density of invertibles in addition. Our algebra C([0,1],C) also has dense
invertibles (standard stable-rank fact); formal target may initially be353909,
whose literal statement does NOT require this extra density hypothesis.
Do not claim formal353908 until density is formally handled or exact scope stated.

Classical complex Sendov is not contradicted, and its2026 proof is not new credit.
This is an obstruction to a single global continuous critical-point choice.

## Explicit strictly interior roots

Take A=C([0,1],C) with pointwise algebra, involution and sup norm.
Let rho=9/10, s=3/4 and u(t)=exp(pi*i*t), 0<=t<=1. Put

    a0(t)=rho, a1(t)=rho*s*u(t), a2(t)=−rho*s*u(t),
    P(z)=(z−a0)(z−a1)(z−a2).

These are three continuous root elements, with norms9/10,27/40,27/40, all
STRICTLY less than1. They are pairwise distinct at every t, because u never
vanishes and s<1. There is no endpoint or missing-critical-root loophole.

## Explicit derivative roots and factorization

Let sqrt denote the principal complex square root, and define

    h(t)=1+(16/27)*conj(u(t))^2,
    q(t)=(3*sqrt(3)/4)*u(t)*sqrt(h(t)),
    Bplus(t)=(rho/3)*(1+q(t)),
    Bminus(t)=(rho/3)*(1−q(t)).

Re h(t)>=1−16/27=11/27>0. Thus principal sqrt(h(t)), and hence q and
both B branches, are continuous. Since |u|=1,

    q(t)^2=1+(27/16)*u(t)^2.

The right side never vanishes: its modulus is at least11/16.
The literal sum-of-deleted-factors derivative is

    P'(z)=3*z^2−2*rho*z−rho^2*s^2*u^2
         =3*(z−Bplus)*(z−Bminus)      for EVERY z in A.

Thus the derivative genuinely splits, and Bplus/Bminus are distinct at every t.
Moreover |q|^2=|q^2|<=43/16<4, so |q|<2 and

    |Bplus|,|Bminus| <=rho*(1+|q|)/3 <rho<1.

Both derivative-root elements lie strictly inside the C*-unit disc.

## ALL critical roots are these two continuous branches

Let b in A satisfy P'(b)=0. The continuous function

    f(t)=(3*b(t)/rho−1)/q(t)

is defined everywhere and satisfies f(t)^2=1. Hence f maps the connected
interval into {−1,1}, so f is constant. Consequently b=Bplus or b=Bminus
as an element of A. Pointwise mixing is impossible because the two branches
never meet. This proves classification of every C*-algebraic critical point,
not merely a statement about the two selected factor roots.

## The source's positive convex-weight hypothesis is satisfied

For B equal to either B branch, B(t) never equals an aj(t). Indeed all
three scalar roots of P_t are simple; at aj the derivative is the product
of the two nonzero differences. Thus each continuous B−aj is nowhere zero
on the compact interval and is invertible in A. Put

    rj(t)=1/|B(t)−aj(t)|^2 >0,
    omega_j(t)=rj(t)/(r0(t)+r1(t)+r2(t)).

Each omega_j is a strictly positive continuous real-valued function, hence a
positive element of A; sum omega_j=1. Since P(B) is invertible and P'(B)=0,

    sum_j (B−aj)^−1=0.

Conjugating and using (B−aj)^−1=conj(B−aj)/|B−aj|^2 gives

    sum_j rj(B−aj)=0,
    B=sum_j omega_j*aj.

This is exactly the source's Equation(1), including genuine positive coefficients
inside A, not scalar pointwise coefficients with no continuity proof.

## No critical point is within distance1 of a0

Let Q=sqrt(43)/4. At t=0, h=43/27>0 and q(0)=Q>3/2;
at t=1, u=−1 and h is unchanged, so q(1)=−Q. In particular,

    Bminus(0)=Bplus(1)=(3/10)*(1−Q),
    |a0(0)−Bminus(0)|=|a0(1)−Bplus(1)|
        =3/5+(3/10)*Q >21/20>1.

Therefore each of the only two critical elements has sup-distance>21/20 from
a0. Neither belongs to D*(a0,1), whose pointwise condition is
|b(t)−a0(t)|^2<=1. This refutes the literal conclusion for the distinguished
root a0 while satisfying every input and derivative-root/weight hypothesis.
Actual margin is3/5+3*sqrt(43)/40 approx1.0918.

## Prior-art status and scope

No prior C*-Sendov refutation was found in the first exact-phrase searches
('C*-algebraic Sendov counterexample', 'Sendov continuous selection',
'Sendov monodromy', 'Sendov C([0,1])'). This is NOT a sufficient novelty gate.
The square-root/branch-switching mechanism itself is classical topology and
receives no novelty credit. Source-paper/citing/companion bodies and possible
subsuming continuous polynomial-selection counterexamples require independent
bounded review. No absolute priority or acceptance claimed.

The result is not the observation that a derivative may have no global root:
here it factors completely, its two roots are in the strict unit ball, the
full positive convex representation is present, and the failure is uniform
proximity for EVERY continuous critical root.
