# Closed formal construction — fresh isolated117/16 replay PASS

The new Lean endpoint is `FlatBernoulli.source_conjecture_319292`:
for every natural n>=12, sourceKappa n < n*sourceKappa(n-1).
Only the rank hypothesis remains. `sourceK` is the source's explicit ordered
composition factorial formula(16), summed over the finite `Composition n`
type and restricted to blocks>=2. `sourceKappa n = n*sourceK(n-1)` is the
source-proved count relation. We do not re-encode the original game positions
or re-prove the author's enumeration of them. At0, the empty composition
contributes1, consistently with Proposition6.7 and the source generating function.

Every bridge below is proved, rather than a final theorem premise:

1. `SourceCompositions`: bijective first-block splitting of all compositions;
   singleton blocks have zero weight; the finite product sum satisfies the
   normalized recurrence and equals renewalCoefficient.
2. `SourceCounts`: every block weight is (b-2)!/b!, so the finite factorial
   count divided by n! equals the normalized composition sum. Final rank shift.
3. `Arrowhead` / `SpectralCompression` / `ArrowheadSpectral`: two actual
   sum-of-squares formulas, [-1,1] spectrum, codimension1 PSD compression,
   at most one negative eigenvalue INCLUDING multiplicity, genuine ONbasis
   center spectral weights/moments.
4. `ArrowheadCriterion`: second moment>=1/2 forces the unique negative
   eigenvalue -q with1/2<=q<=1; finite even/odd quantitative propagation.
5. `ArrowheadGrid` / `ArrowheadRecurrence`: actual nodes i/N and square-root
   coupling, exact normalization/second moment and exact center walk convolution.
6. `GridPowerLimits` / `GridKernel`: the approximation is proved algebraically
   using the pinned classical Faulhaber identity, not an assumed Riemann theorem.
   Specifically M_N(k)=(1/N)sum(i/N)^k is a finite polynomial in1/N with
   constant1/(k+1); hence gridKernel_N(k)=M_N(k)-M_N(k+1) tends to
   1/((k+2)(k+1)). Induction through the exact convolution gives convergence
   of every actual center moment to renewalCoefficient.
7. `RecurrenceBase` / `RenewalTail`: kernel-checked exact values at indices
   0..14; strict base tests at3/12/14; eventual finite-grid hypotheses; uniform
   negative bounds survive passage to the limit, giving all n>=11.

This finite-power-sum implementation replaces the mathematical proof's generic
Riemann-sum step with an exact classical formula for the same matrices. The36 original reviewed bytes are preserved via preliminary-reviewed-file-locations.json; PROOF.md has the two small exposition fixes. New sources are outside the original freeze. No novelty PASS or discovery acceptance is claimed. Source game
counts use the source-established enumeration; the literal finite formula is
fully formalized. Fresh isolated replay PASS; all117 type/axiom reports inspected, all16module logs0, standard3axioms only. See verification/parent-audit.json and full117-Checks.log.
