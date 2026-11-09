# W010 Jacobi selector — parent disposition

2026-10-08. C (Opus) terminal report read; all 13 artifact hashes verified.
Accept equations (1)–(5), exact p=167,q=5 certificate and preservation of
the unfiltered training invariant when filtering is used only for final
tests. No candidate run, reachable-law certificate or factoring improvement.

The [review](W010-jacobi-review.md) correctly distinguishes same-stage
quadratic-factor tests from an endpoint product. Its no-full-gcd claim
requires those factors to be tested separately: earlier root absorption
at the other prime can mask an endpoint product. Using all stage factors
costs additional gcds. Square moduli need separate handling. The beta-gcd
formula is a raw joint probability with both anchor charts legal, not a
probability conditioned on that event.

Root mass and total collision mass remain pointwise nondecreasing. The
residual mass v can decrease in expected value under the filter. Its sign
depends on the other prime's character-sector ratio. The named rational
and integral p-laws have threshold L_(q,+)/L_(q,-)<5/72. With a UNIFORM
q-state this fails for q>=11; that scoped qualification is accepted.

Two broader statements in the report need repair:

1. For N=35 at the uniform start, no filtered update is accepted. Among
   attempts whose anchor chart is clean, beta gcd is the remaining progress
   channel. The original anchor gcd tests can themselves find a factor;
   beta gcd is not the only success channel of the complete protocol.
2. A nonuniform partner counterexample does not require a search. The
   parent constructs one below. The small UNIFORM partner in the original
   certificate is not an essential limitation of the distribution-level
   falsifier. No version establishes reachability by the cubic rule.

## Explicit nonuniform partner at q=173

Use the integral p=167 law already checked by C: t=14/167 at each of
+-3,+-5, H=42/167 at each of +-7, and zero mass 27/167. Its positive
sector drift is D_(p,+)=-40t^4 and L_(p,+)=8t^2.

At q=173 put weight r=43/173 at each of +-1,+-2 and mass 1/173 at zero.
The only legal norm parameters are Q(1,2)=7 and Q(1,-2)=3, each with
four sign/interchange pairs and K=4r^2. Euler's criterion gives -1 for
both 3 and 7 modulo 173. Thus

    L_(q,+)=0, L_(q,-)=8r^2>0,
    raw filtered p drift = -320t^4 r^2 < 0,
    accepted p drift = -5t^2 = -980/27889.

The [exact certificate](W010-jacobi-parent-certificate.json) verifies
primality of this one named q by trial division, both character values,
and rational arithmetic. It performs no candidate run or parameter sweep.
Both laws have integral fiber counts and can be pushforwards of odd maps.
At q, assign the 86 nonzero input sign-pairs as 43 to +-1 and 43 to +-2.
At p use the review's 13/14/14/42 assignment of its 83 input sign-pairs.

If desired, interpolate these odd functions and make both polynomials
monic of degree 243 by adding X^76(X^167-X) and X^70(X^173-X),
respectively. Coefficient CRT gives one monic odd map modulo 167*173.
Having degree 3^5 does NOT show it is a composition of five accepted
W010 cubics; interpolation uses the diagnostic factors and is not a
candidate construction. The obstruction is an unconstrained sector law,
not proof of a reachable bad state or a failure at large input sizes.

## Retained computation and next obligation

Keep unfiltered training. A final filtered quadratic-factor test has
post-chart raw probe-success probability L_(q,-)G_p+L_(p,-)G_q, plus any
separately counted earlier anchor/beta-gcd successes. Its rejection cost
and lost both-square successes remain charged. The formula supplies no
advantage over the batch pair detector. A useful final selector needs a
paid reachable sector distribution or a demonstrated saving in probe work;
the no-full-gcd property alone does not provide either.
