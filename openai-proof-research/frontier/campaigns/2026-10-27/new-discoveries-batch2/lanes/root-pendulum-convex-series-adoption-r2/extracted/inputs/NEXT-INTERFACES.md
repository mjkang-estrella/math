# Remaining pendulum components

Preserve the four inherited mathematical modules byte-identically and use their literal definitions. SourceClaim is closed-interval convexity, not merely convexity of a surrogate series.

## Convexity and series component

For every a>0 and n:Nat, prove ConvexOn Real (Ioi 0) (moment n a). Handle n=0 with moment_zero, n=1 with moment_one and concavity of sqrt. For n>=2, use the fixed-cutoff first integral and the moving-cutoff second integral. The latter has the positive-part representation integral over y>=0 of (max (z-y) 0)^(n-1/2) / sqrt(a+y). On any Jensen triple, truncate to a common finite bound above the three z values and justify integrability/substitution. Real.rpow at zero and literal natural-power momentKernel require a genuine equality proof; do not assume it.

Define weight n = (Nat.choose (2*n) n : Real) / 8^n. For 0<a<2 and 0<z<2 prove the convergent series identity

transformedTime a z = (1/(2*sqrt 2)) * tsum (fun n => weight n * moment n a z).

Use actual binomial-series convergence and justified integral/sum exchange (positive monotone sums or another sound route). Natural coefficients, all-index positivity, summability and integrability must be closed. Deduce transformedTime convex on Ioo 0 2 and then sourceTime phi convex on Ioo 0 2 for 0<phi<pi/2. No endpoint theorem is required from this component. No strictness or C2 strengthening required.

## Endpoint component

For every 0<phi<pi/2 prove ContinuousOn (sourceTime phi) (Icc 0 2), or sufficient literal one-sided endpoint limits together with the closed convexity transfer. Prove a closed interface

sourceClaim_of_interior_convex :
 (forall phi, 0<phi -> phi<pi/2 -> ConvexOn Real (Ioo 0 2) (sourceTime phi)) -> SourceClaim.

The premise is a separately assigned component, not an unconditional SourceClaim. Show endpoint integrability; totalized interval integrals cannot silently stand in for divergent integrals. At z=0 the first kernel has an integrable inverse-square-root singularity at x=phi; the moving interval contributes at most b(z)/sqrt(a(phi)). At z=2 use a uniform positive denominator for nearby z and varying-cutoff dominated convergence. Use literal source endpoint values, not a definition by continuous extension. Interior continuity may follow from direct integration, or from convexity when proving the conditional transfer. Do not duplicate higher moments or series work.
