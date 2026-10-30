# Gaunt's sharp modified-Bessel tail bound: complete ordinary proof candidate

28 October 2026. **Credit 0; unreviewed candidate, not accepted.** No full Lean
endpoint, manuscript or packet is claimed. Classical convexity is uncredited.

## Exact question and scope

R. E. Gaunt, *Inequalities for some integrals involving modified Bessel
functions*, arXiv:1806.00524v2, Conjecture 2.4 and Remark 2.5, printed p. 7.
The actual PDF page was rendered and visually read. Latest arXiv history is
v2, 9 October 2018. Journal citation: Proc. Amer. Math. Soc. 147 (2019),
2937–2951, DOI 10.1090/proc/14433. Published-body comparison is pending.
The source conjecture is MathDB 339406. Its live API record was fetched on
28 October 2026: open, progress null and all resolution/comment arrays empty.
That is a status observation, not novelty evidence.

For real n<1 and nu >= 1-n+sqrt(2(1-n)), put

    mu=nu+n,  delta=sqrt(mu^2-2*nu-1).

The conjecture asks for every x>0

    integral_x^infinity t^(-nu) K_mu(t) dt > x^(-nu) K_delta(x),       (1)

and asserts that delta is the largest possible absolute order on the right.
We prove both, including the boundary delta=0. In fact, under the same source
hypotheses, the strict bound with an arbitrary real order eta holds for all x>0
if and only if |eta|<=delta. This is one combined source outcome, not multiple
credits for optimality, derivative comparisons, or parameter instances.

## 1. Elementary convexity in squared order

For fixed x>0, set F_x(lambda)=K_(sqrt(lambda))(x), lambda>=0. The classical
Schlafli representation is

    F_x(lambda)=integral_0^infinity exp(-x cosh u) cosh(u sqrt(lambda)) du.

For u>0, lambda -> cosh(u sqrt(lambda)) is strictly convex on [0,infinity):
its entire power series is sum_(j>=0) u^(2j) lambda^j/(2j)!, and all
coefficients are positive. In particular the quadratic term is strictly
convex and the remaining terms are convex. Equivalently, for lambda>0 its
second derivative is

    u [u sqrt(lambda) cosh(u sqrt(lambda))-sinh(u sqrt(lambda))]
      /(4 lambda^(3/2)) > 0,

since z cosh z-sinh z has derivative z sinh z>0 and value zero at z=0.
At zero the second derivative is u^4/12>0. Integrating the strict convexity
inequality against the positive weight makes F_x strictly convex.
All integrals converge: exp(-x cosh u) dominates every fixed exponential in u.
For the derivative at lambda=1, dominated differentiation on a compact
lambda-neighborhood is justified by the same estimate with polynomial factors.

This is an elementary use of the classical integral representation. It is
not advertised as a new special-function convexity theorem.

## 2. Parameter geometry

The source threshold gives mu-1 >= sqrt(2(1-n))>0. Hence mu>1 and

    delta^2=(mu-1)^2-2(1-n)>=0,
    nu^2-delta^2=(1-n)(2nu+n+1)>0.

Here nu>0 and 2nu+n+1>0 follow directly from the threshold. Thus

    0<=delta<nu,   mu^2=delta^2+2nu+1>(delta+1)^2.

These inequalities hold also when n is negative; no hidden n>=0 or
integer-n assumption is used.

## 3. The missing derivative comparison

First suppose delta>0. Set a=(delta-1)^2, b=(delta+1)^2, c=mu^2.
Then 0<=a<b<c. Strict convexity gives the extrapolated-chord inequality

    F_x(c) > F_x(a)+(c-a)/(b-a) [F_x(b)-F_x(a)].

Using K_(-r)=K_r and the standard recurrence

    K_(delta+1)(x)-K_(delta-1)(x)=2delta K_delta(x)/x,

and observing c-a=2(nu+delta), b-a=4delta, we obtain

    K_mu(x) > K_(delta-1)(x)+(nu+delta) K_delta(x)/x.                (2)

At delta=0 the two chord nodes coincide, so division by delta is invalid.
Instead use the strict supporting-tangent inequality at lambda=1:

    F_x(mu^2)>F_x(1)+(mu^2-1)F_x'(1).

Integration by parts gives

    F_x'(1)=(1/2) integral_0^infinity u sinh(u) exp(-x cosh u) du
           = K_0(x)/(2x),

because d_u exp(-x cosh u)=-x sinh(u) exp(-x cosh u), and
u exp(-x cosh u) vanishes at both endpoints. Since mu^2-1=2nu,
this yields K_mu(x)>K_1(x)+nu K_0(x)/x, exactly (2) at delta=0.

The usual derivative formula K_delta'=-K_(delta-1)-delta K_delta/x now gives

    d_x[x^(-nu)K_delta(x)]
      =-x^(-nu)[K_(delta-1)(x)+(nu+delta)K_delta(x)/x]
      >-x^(-nu)K_mu(x).                                          (3)

This proves the comparison marked with a question mark in source (2.18)
for every admissible parameter, including its removable zero-order case.

## 4. Integrating proves the literal tail inequality

For fixed x>0 all functions are continuous on [x,infinity). Modified Bessel
decay at infinity makes the tail integrable and x^(-nu)K_delta(x)->0.
Integrating (3) from x to infinity therefore gives (1), strictly: its
continuous positive difference has positive integral already on any
nontrivial finite subinterval. Equivalently the exact identity is

    integral_x^infinity t^(-nu)K_mu(t)dt-x^(-nu)K_delta(x)
      =integral_x^infinity t^(-nu)
         [K_mu(t)-K_(delta-1)(t)-(nu+delta)K_delta(t)/t]dt>0.

No differentiation with respect to source parameters, numerical sign test,
or assumed derivative comparison enters this proof.

## 5. Optimal absolute order

If |eta|<delta, the same integral representation gives K_eta(x)<K_delta(x)
for every x>0 (cosh is strictly increasing with positive order). Thus (1)
implies the strict inequality at eta. The orders +/-delta give equal right
hand sides by evenness, and (1) covers them.

For the converse, the standard fixed-order large-x expansion is

    K_r(x)=sqrt(pi/(2x)) exp(-x)
             [1+(4r^2-1)/(8x)+O(x^(-2))].

One integration by parts, with the O-term controlled uniformly on t>=x
for each fixed order and parameter, yields

    integral_x^infinity t^(-nu)K_mu(t)dt
      =sqrt(pi/2) exp(-x) x^(-nu-1/2)
        [1+((4mu^2-1)/8-nu-1/2)/x+O(x^(-2))].

The coefficient in parentheses is (4delta^2-1)/8. Consequently

    integral_x^infinity t^(-nu)K_mu(t)dt-x^(-nu)K_eta(x)
      =sqrt(pi/2) exp(-x) x^(-nu-3/2)
        [(delta^2-eta^2)/2+O(x^(-1))].

If |eta|>delta the leading constant is negative, so the proposed lower bound
fails for every sufficiently large x. This proves the iff and the source's
two best shifts beta=mu-delta and beta=mu+delta. The source's n=1 equality
is already known and is uncredited; it is outside the strict n<1 theorem.

## Validation, eligibility objections and gaps

The proof is complete as an ordinary argument based on the classical
Schlafli integral, Bessel recurrence/derivative formulas and fixed-order
asymptotics. The main new-to-this-lane observation is extrapolation in
**squared** order, which produces exactly the conjectured discriminant.
The source's integer-shift argument is not being silently extended.

Strongest objection: this may be a routine instance of an existing published
order-squared convexity or three-order Bessel inequality. Classical machinery
and shortness alone are not novelty evidence either way. An independent
review must explicitly screen that bridge and the author's subsequent works.
Initial exact-title/conjecture and squared-order searches located no resolution;
this is a bounded initial search, not novelty clearance. The journal conjecture
body, citation corpus and public formal registries remain to be checked.

Full literal Lean formalization remains absent. A credible endpoint can define
K by its actual convergent integral and prove the literal improper tail bound;
it must discharge integrability, recurrence/derivative, order convexity and
infinity limits rather than assume them. The optimal-order asymptotic bridge
also needs a genuine formal proof if that part is included in acceptance.
No conditional helper theorem can substitute for these obligations.
