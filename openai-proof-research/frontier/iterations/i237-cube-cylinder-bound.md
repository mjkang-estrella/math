# I237 — cube cylinder bound, proof and contribution screen

2026-10-12. **Mathematical verdict: correct. Contribution verdict: technical corollary; do not count as the tenth substantial finding.** Nine accepted findings remain nine. No claim of worldwide novelty or of a published best cube constant is made.

## Exact statement and proof outcome

For every finite cover of C=[-1,1]^3 by cylinders B_i+R u_i, where u_i is a Euclidean unit vector and B_i is an arbitrary Lebesgue-measurable subset of u_i-perp,

    sum_i area(B_i) >= 2sqrt(3).

Infinite-area bases are harmless. For finite-area bases, Tonelli applied to the nonnegative density

    f_R=1_C 1_{|x|<R}/sqrt(R^2-|x|^2)

proves the claim. Set f_R=0 on the sphere. Its line integrals are bounded by pi, including tangent lines. For 1<=R<=sqrt(2), the six omitted face caps have disjoint interiors and

    integral_C f_R / pi
      = pi R^2-6R^2 arccos(1/R)+6sqrt(R^2-1).

The derivative is 2R(pi-6arccos(1/R)); its maximum on this interval is 2sqrt(3), at R=2/sqrt(3). The cube's minimum projection area is 4, so the absolute normalized lower bound is sqrt(3)/2. This is not a directionwise normalized inequality. There is no unpaid proof step in this lower bound; no claim of optimality among all densities or all radii is made. [Full analytic record](../experiments/i237_cube_cylinder_bound/analytic-attempt.md).

## Primary comparison

Bezdek–Litvak (2009), Theorem 3.1 and its proof, already provide exactly the singular-ball density, constant line integral pi, and measure comparison. Their ball theorem gives the old inscribed-ball consequence pi for this cube. I237's calculation increases that consequence by the factor 2sqrt(3)/pi. The general 1/3 theorem is a weaker benchmark here. A coordinate-axis square cylinder gives the upper bound 4; an arbitrary-axis lower bound of 4 was not established in the primary sources read. Failure to locate one does not prove that it is unknown.

The 2016 packing companion's Theorem 3.1 adds covering multiplicity; its other relevant theorems are packing statements. Ball's symmetric-body result concerns planks. Falconer's sectional optimization is by hyperplanes, which are planes in dimension three, not the lines needed here. The later Akopyan–Karasev–Petrov version (v3, 2019), Section 8, concerns ball certificates; the symplectic subadditivity statement remains a conjecture with different objects. These do not justify importing a cube constant of 4. [Primary copies and precise reading record](../sources/i237_cube_cylinder_bound/literature.md).

## Upstream connection and non-duplication

Actual theorem statements and relevant comparison sections of all four pinned cylindrical-cover companions were read from fresh copies retrieved at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. They use the same finite measurable-base area model. The standalone cube proof needs no new pinned theorem.

There is a real, but immediate, upstream corollary: if a ruled family satisfying the exact hypotheses of the pinned finite-approximation Theorem b:approximation contains C after the physical map F_h, then its integral projection cost h integral_D J_h(V) is at least 2sqrt(3). Apply finite approximation at every positive tolerance, then the cube inequality, and let the tolerance vanish. This is a barrier for cube-cover designs in that family, not a new realization mechanism.

R015 and its I212 source record were read solely for duplicate-counting and method comparison. R015 already owns the tetrahedral lower theorem and optimal quadratic envelope. The cube is a different body and uses a different density, but changing those choices does not by itself earn an additional substantial finding. Here the new step is elementary cap subtraction and scalar optimization of an old certificate; no nonroutine bridge arose. General boxes, similarities, countable/weighted covers, and the ruled-family obstruction would be technical variants, not additional findings.

## Deliverables and limits

- [Analytic attempt](../experiments/i237_cube_cylinder_bound/analytic-attempt.md): complete proof, exact scope, benchmark comparison, real upstream implication, unpaid work.
- [Reading and failures](../experiments/i237_cube_cylinder_bound/reading-and-failures.md): search families, exclusions, access failure, decision.
- [Literature record and primary copies](../sources/i237_cube_cylinder_bound/literature.md).
- [Input authentication](../experiments/i237_cube_cylinder_bound/input-authentication.json): detached SHA-256 values and pinned Git blob checks. No self-hash, seal, snapshot, experiment, test, staging, commit, publication, or subordinate agent.

Do not manufacture acceptance: the correct elementary inequality is retained for reference, with contribution status **not sufficient**.
