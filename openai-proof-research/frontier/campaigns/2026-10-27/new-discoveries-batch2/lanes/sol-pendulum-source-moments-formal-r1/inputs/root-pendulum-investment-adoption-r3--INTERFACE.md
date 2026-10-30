# First formal component: literal source and exceptional moments

Use namespace PendulumTimeMap. Definitions must denote actual real interval/Lebesgue integrals, never the desired series or claimed value. Suggested canonical definitions, with harmless totalized endpoint values:

- b(z)=Real.arccos(1-z)/2; a(phi)=1-Real.cos(2*phi).
- sourceTime phi z = integral x=0..phi of (sqrt(z-cos(2phi)+cos(2x)))^-1 + integral x=0..b(z) of the same function.
- transformedTime a z = (1/2) times the sum of integrals t=0..a and t=0..z of (sqrt(t*(2-t)*(a+z-t)))^-1.
- moment n a z = sum of integrals t=0..a and t=0..z of t^n / sqrt(t*(a+z-t)), with n a natural exponent. On positive t this is exactly t^(n-1/2)/sqrt(a+z-t). Values at isolated endpoints must not change the integral.
- SourceClaim = for every phi with 0<phi<pi/2, ConvexOn Real (Set.Icc 0 2) (sourceTime phi).

Mandatory initial component: (1) exact source definitions and basic parameter/endpoint ranges; (2) integrability of both moment pieces for every natural n, 0<a<2,0<z<2, and transformed/source pieces in the interior; (3) sourceTime phi z = transformedTime (a phi) z on the interior; (4) moment 0 a z = pi and moment 1 a z = pi*(a+z)/2-2*sqrt(a*z). Prove substitutions/integrability, do not take them as premises.

The final SourceClaim is a later integration target, not a mandatory claim for this component. If time permits prove the literal endpoint continuity independently, but do not jeopardize the source/low-moment obligations by scattering into optional work. No need for strictness or curvature estimates. Subsequent components will prove convex higher moments, positive series/MCT, and continuous-extension closure. Definitions should be stable and export exact types for composition.

Prove the interval integral endpoint behavior carefully; a formula for arbitrary totalized nonintegrable integrals is not enough. Preserve literal phi/z parameterization and both closed endpoints in SourceClaim. A theorem conditional on an unproved change-of-variables identity is not a completed bridge.
