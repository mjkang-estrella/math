# Pendulum literal endpoint transfer — finite component

Status: mandatory endpoint proofs closed; 11 mathematical modules and 88 actual declarations pass strict local compilation and the exhaustive actual-origin/type/axiom/safety audit. The accompanying replay receipt records the fresh source-only extracted replay result.
Credit 0. No unconditional SourceClaim, acceptance, novelty clearance, paper, public action, or count change.

## Exact interfaces

For every real phi with 0 < phi < Real.pi/2:
- source_integrable_zero proves IntervalIntegrable (sourceKernel phi 0) volume 0 phi.
- moving_source_integrable proves IntervalIntegrable (sourceKernel phi z) volume 0 (b z) for every z in Icc 0 2.
- source_integrable_two proves integrability of both actual source kernels at z=2.
- source_integrable_closed proves integrability of both actual source kernels for every z in Icc 0 2.
- sourceTime_continuousWithinAt_zero proves the literal right endpoint continuity within Icc 0 2.
- sourceTime_continuousAt_two proves even unrestricted continuity at 2.
- sourceTime_continuousOn proves ContinuousOn (sourceTime phi) (Icc 0 2), with no convexity premise.
- sourceClaim_of_interior_convex has precisely the type
  (forall phi : Real, 0<phi -> phi<Real.pi/2 ->
    ConvexOn Real (Ioo 0 2) (sourceTime phi)) -> SourceClaim.

The last theorem does not discharge its premise. Higher-moment convexity, the convergent binomial expansion, and hence unconditional SourceClaim remain assigned elsewhere. Historical fixed-interval coverage, missing registry-tree/patch coverage, publication/novelty limits, and final acceptance gates remain open as recorded by root. No strictness or derivative claim is made.

## Literal singular endpoint proof

Defs, Substitution, Moments, and Source are inherited byte-identically from sol-pendulum-source-moments-formal-r1. The predecessor source-only archive has SHA256 05cef5c6617e1372f925340e70d5f4c5444afe2844840eb0fbc8ac902bd5fcb0. All definitions retain totalized real square roots, inverses, and interval integrals.

ClosedSubstitution extends the genuine change-of-variables theorem to q <= pi/2. At q=pi/2 and c=a(phi)>0, weight w(t)=1/sqrt(2-t) is continuous on [0,a(phi)], because a(phi)<2. The theorem proves integrability of w(t)/sqrt(t*(a(phi)-t)) all the way through its singular endpoint; it does not assume that integrability. A second genuine derivative change of variables with c=2 proves integrability of the literal sourceKernel phi 0 on [0,phi]. Equalities only on the open integration interval legitimately ignore endpoint singleton values.

For the fixed source integral at zero, the strict cosine inequality makes the denominator positive for x<phi. Its value at z>=0 is dominated by the proved integrable z=0 kernel. Dominated convergence ignores the singleton phi and proves continuity at the actual totalized endpoint integral.

For the moving integral, cos(2x)>=cos(2*b(z))=1-z on [0,b(z)] gives the uniform squared-denominator bound a(phi)>0. A globally continuous auxiliary kernel replaces the denominator by its maximum with a(phi)/2; on every actual moving interval for z in [0,2] this is exactly the literal source kernel. The continuous parametric primitive composed with continuous b therefore proves continuity on all of [0,2], including the collapsing zero interval.

At z>=2-a(phi)/2 the squared denominator is >=a(phi)/2 for every real x. A similar globally continuous auxiliary kernel is exactly the literal source kernel near 2, for both fixed and moving integrals. Positive-z continuity of the fixed integral follows with a z0/2 clamp on [0,phi]. Together these yield unconditional closed-interval continuity.

Finally, convexOn_Icc_of_interior passes the Jensen inequality along inward affine perturbations c(t,x)=(1-t)*x+t as t tends to zero from above. These lie in (0,2), respect every Jensen combination, and converge to the actual endpoint values by the proved continuity. No endpoint is defined by a limit.

## Resources, provenance and qualifications

All edits, retrievals, hashes, packaging, extraction and checks use the unchanged helper guard at sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py with one-thread numeric environment and PYTHONDONTWRITEBYTECODE=1. Helper AS/RSS is 512 MiB, CPU 210 seconds, wall 230 seconds. Every Lean compile is serial j1, M2700, warningAsError=true, autoImplicit=false through the byte-identical predecessor guard; sampled group RSS ceiling 2800 MiB, CPU 210, wall 230, nominal 45 ms sampling. Unsampled transients are not excluded. No cap increases, child agents, network research, browser, messages, git, shared edits or uploads.

Pins, compiler binary hash, mathlib revision and eight companion revisions are inherited unchanged. FullAudit enumerates actual mathematical module origins, including generated/private declarations, and compares module-data inventory with the enumerated names. It prints actual types and transitive axioms and rejects unsafe, partial or axiom flags and any axioms outside propext, Classical.choice, Quot.sound. Actual upstream olean/private/server dependencies are hashed. The extracted replay compares actual audit rows and actual dependency hashes.

Frozen originals are checked against root-pendulum-moments-adoption-r1/review-freeze.json before and after. Input records link byte-identical inherited modules, guards, pins, original proof, ordinary reviews, root endpoint supplement and NEXT interface to actual originals. Failure source snapshots and diagnostics are preserved in attempts.

Initial helper invocation with --help failed because the guard executes its arguments rather than parsing flags; no resource limits were changed. A search for a nonexistent Parametric.lean failed and the correct DominatedConvergence.lean was used. A premature audit parse before FullAudit finished failed due to missing AUDIT_TOTAL; the completed audit must be used. These setup/check failures have no mathematical status.
