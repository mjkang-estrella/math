# The exact opening/cap interface and a linear obstruction to a shortcut

Myeongjin Kang. Original prose CC BY 4.0. Author-side calculations only.
The full target T355E remains unproved and unrefuted.

## A sufficient joint matching estimate

Fix a limit shrinker S and its source355 stationary chart p=(b,x). Assume
that this chart and the localized proposition apply to S in their actual
scope. Consider exact shrinkers Σ_i converging locally smoothly to S,
with observations p_i tending to zero. A sufficient additional estimate
for excluding a changing end is the following pair, for some fixed
c₀,c₁,a,A>0 and numbers D_i tending to infinity:

1. The ENTIRE intersection of Σ_i with B_{c₀D_i^a} is a weak small-height,
   small-slope graph over S_{b_i}, with the source's fixed chart tolerances.
2. |x_i|≥c₁D_i^(−A).

The constants may depend on S and the sequence. Uniformity over all S is
not needed for T355E. Every end must enter the same complete graph in(1):
working on one axial tube while ignoring other ends is insufficient.
An anticipated matching scale for a cap is a=1,A=2, but even some positive
a and finite A would suffice. Neither estimate is asserted proved.

Indeed entropy≤Λ gives a common quadratic area-ratio bound: choose the
Gaussian centered at y with scale r², bound its integrand below by e^(−1/4)
on B_r(y), and obtain area(Σ_i∩B_r(y))≤4πe^(1/4)Λr². For an exact shrinker
its defect Φ is zero. Source Proposition flow:localized, with any fixed
allowed η>0 and its fixed γ>0, would give

    |x_i| ≤ C exp(−(1−η)γ c₀²D_i^(2a)/8).

This contradicts(2), since D^A exp(−cD^(2a)) tends to zero for c,a>0.
This last contradiction is elementary and technical. It does not prove
the matching estimates and is not nominated as a theorem.

If x_i=0, the proposed lower bound fails, rather than being automatically
provided by a distant cap. This zero case cannot be silently dropped.
The source also permits an empty opening list, in which case this route
has no nonzero x to exploit. No alternate end type or smaller target is
substituted.

## The scalar cylindrical equation has a dangerous second mode

For a rotational radius graph r(z)>0 over an axial half-line, the
self-shrinker equation in the source normalization is

    r″/(1+r′²) − (z/2)r′ + r/2 − 1/r = 0.

At the round cylinder r=√2 its linearization is

    L₀u := u″ − (z/2)u′ + u = 0.                          (1)

The slow solution is φ(z)=z²−2. Fix z₀>√2 and set

    ψ(z)=φ(z) ∫[z₀,z] exp(t²/4)/φ(t)² dt.                 (2)

Reduction of order gives L₀ψ=0 and W(φ,ψ)=exp(z²/4), so these solutions
are independent. The asymptotic is

    ψ(z) ~ 2 exp(z²/4) z^(−3)       as z→∞.              (3)

For completeness, the integral in(2) is asymptotic to
2 exp(z²/4) z^(−5). Both quantities tend to infinity. The derivative of
the latter is exp(z²/4)z^(−4)(1−10/z²), whereas the integrand is
exp(z²/4)(z²−2)^(−2); their ratio tends to one. L'Hôpital's rule proves
the integral asymptotic, and multiplication by φ gives(3).

For D>z₀, normalize u_D(z)=ψ(z)/ψ(D). Then u_D(D)=1, while on each fixed
compact interval K⊂[z₀,∞), for every fixed integer k,

    ||u_D||_{C^k(K)} = O_K,k(D³ exp(−D²/4)).              (4)

Its coefficient of φ in the fixed basis (φ,ψ) is exactly zero. The
C^k bound follows because ψ and its fixed derivatives are bounded on K;
(3) gives the denominator. Thus a perturbation with no polynomial opening
coefficient can be invisible to every fixed-order compact observation
while changing the outer geometry by order one. In particular there is
no general polynomial core-to-outer estimate for solutions of(1).

For fixed 0<α<1, (3) also gives

    u_D(αD) ~ α^(−3) exp(−(1−α²)D²/4) → 0.              (5)

This is a linear diagnostic, NOT a family of actual nonlinear complete
embedded self-shrinkers or a counterexample to T355E. Global geometry
may exclude it. It specifically invalidates inferring a polynomially
large slow coefficient from a transition distance using local elliptic
regularity alone.

## What Sun–Wang actually supplies, and what still has to be proved

In Sun–Wang1811.05387v2, Theorem3.1 allows a cylindrical limit end to
correspond either to an annular end or a disk in Σ_i. Proposition5.7
handles the disk case. Let d_i be the largest distance in that conical
neighborhood and y_i the corresponding direction. Step2 states that for
ρ_i→∞ with d_i(d_i−ρ_i)→∞,

    (Σ_i−ρ_i y_i)/sqrt(1−ρ_i²/d_i²)

converges locally smoothly to a round cylinder, along subsequences; at the
tip scale the limit is a bowl translator. In particular at ρ_i=αd_i,
the physical cylindrical radius tends to √2 sqrt(1−α²). That is different
from the pure growing linear mode(5), whose radius change is negligible
at every fixed fraction of D. The primary result therefore provides real
global information, and the mode example must not be read as defeating it.

However this is convergence after translating/scaling at moving points.
It does not identify the coefficient x_i defined by the source's compact
observations. Taking α small after i→∞ does not give a remainder estimate
uniform as α=α_i→0. The source itself states that fixed jet orders and
parameter neighborhoods are chosen before other limits. Exchanging these
orders would manufacture the missing estimate.

A proof would need to match the macroscopic cylinder/bowl profile through
a long intermediate region to the compact normalized chart, controlling:

- the exponentially growing radial mode(2);
- the independent tilt and angular modes on every end;
- the compact source multipliers and observation constraints;
- the chart change from the actual directions y_i to S_{b_i}; and
- simultaneous conical or cap degenerations on other ends.

An angular average does not commute with the nonlinear geometric equation.
A single radial ODE calculation cannot establish these requirements for
the unchanged, nonsymmetric target.

## Why the source's real comparison does not close this gap by itself

Lemma ref:real-comparison assumes a complete weak graph to a radius R
and retains the annular term

    a_R = ||(1+|Y|)|∇(u−v)|+(1+|Y|)²|u−v|||_{L²_a(annulus)}.

It yields a weighted H² and multiplier estimate by the residual,
observation error, |x|^(M+1), and a_R. For bounded annular data, a_R is
exponentially small in R². This is an upper estimate; it supplies no
polynomial lower bound on |x| in terms of the maximal graphical radius.
Equation(4) illustrates why such a reversal cannot come from the Gaussian
estimate alone. Cutting off a Taylor graph at |x|^(−σ_M) is a construction
of a comparison surface, not a proof that Σ_i stays graphical to that
radius. The cutoff construction cannot be inserted as the missing
hypothesis(1).

No uniform finite-jet degree, weighted compactness of all end charts, or
quantitative slow-mode matching is proved in this packet. The exact full
end-stability target stays unchanged and open here.
