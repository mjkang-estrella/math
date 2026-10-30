# Gaunt supporting component: 20 declarations, not the source conjecture

28 October 2026. Credit0. This is root-authored supporting infrastructure for
the unaccepted ordinary candidate in root-gaunt-integral-r16. No independent
review, source/novelty/substantive clearance, manuscript, final packet or
complete source endpoint is claimed.

## What the actual Lean types prove

`formal/SquaredOrder.lean` proves strict convexity on lambda>=0 of the literal
function cosh(u sqrt(lambda)) when u!=0, using the genuine convergent cosh
power series and the strict quadratic term. It proves the extrapolated chord
inequality and the derivative/tangent comparison at lambda=1, with no false
division by the zero-order parameter.

`formal/IntegralBase.lean` defines

    besselK(v,x)=integral_(u>0) exp(-x cosh u) cosh(vu) du.

It proves its integrand integrable on all of R for every real v and x>0,
by the explicit Gaussian domination

    exp(-x cosh u) cosh(vu)
      <= exp(|v|^2/x) exp(-(x/4)u^2).

It then proves strict convexity of lambda -> besselK(sqrt(lambda),x) by a
strict integral comparison with positive support. Evenness, removal of sqrt
of a square, and the closed three-order inequality follow:

    x>0, d>0, d<v, m^2=d^2+2v+1 =>
    (v+d)K_(d+1)(x)+(d-v)K_(d-1)(x)<2d K_m(x).

This uses the actual convergent integral, not an abstract function assumed
convex or a residual integrability hypothesis. The arithmetic relation is the
intended parameter premise of this supporting inequality, not a full source
conjecture endpoint.

## Verification actually performed

Run from this lane:

    python3 verify_component.py

The script verifies the absolute Lean binary SHA/version, all eight dependency
revisions and clean dependency trees against pins.json. It copies only the two
Lean sources, Checks.lean and the runner to a fresh temporary directory, builds
both modules with warnings as errors, and reads every one of 20 type/axiom
reports. No local prebuilt oleans are copied or consumed. Both module logs are
empty; the script exits0. All 20 actual reports were read by root and list only
propext, Classical.choice and Quot.sound. Banned proof shortcuts are absent.

Authoritative receipt: verification/audit.json. Actual type/axiom displays:
verification/Checks.log. Compiled artifacts in formal/ are supporting local
outputs and are not the fresh replay inputs.

## Exact remaining formal obligations

1. Bessel recurrence and derivative with respect to its positive argument,
   proved for the actual integral above (integration by parts and dominated
   differentiation), not assumed.
2. The zero-order integral identity
   integral_0^infinity u sinh(u) exp(-x cosh u)du=K_0(x)/x, allowing the already
   proved scalar tangent inequality to give the boundary Bessel comparison.
3. Source parameter geometry, literal t^(-nu) tail integrability, infinity
   boundary values, and the FTC integration yielding GauntConjecture2.4.
4. If included in the formal source endpoint, the optimal-order converse
   requires genuine fixed-order asymptotic control; no formal asymptotic
   theorem is present here.
5. The integral is a classical canonical representation of K. Any review
   requiring a bridge to the source's series/limiting definition must identify
   and discharge that requirement explicitly; it is not silently asserted.

The entire ordinary proof, including the zero-order boundary and optimality,
is written separately. Its short classical-convexity mechanism has a serious
routine-corollary objection still to be adjudicated independently. These
supporting declarations receive no discovery credit regardless of disposition.
