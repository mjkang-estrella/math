# I270 — independent contribution review of the nonlinear ball–tube contact limit

2026-10-12. **Verdict: SUBSTANTIAL.** This is the CONTRIBUTION gate for the full I249/I253/I263 theorem, assessed as one prospective finding. It is not a proof PASS/FAIL, an acceptance decision, or a count increment. The supplied project status remains ten accepted toward twenty substantial findings. No prior independent contribution verdict for this full limit is inferred from I249's unresolved disposition or I253's technical recovery.

The original I249 analysis and the complete I263 analysis were read, with their required SHA256 values directly matched. I253's complete recovery, I263's complete report, read log, authentication JSON, and literature record were read. No I269 or other live sibling output was read.

## The contribution being assessed

On the unit cubic flat torus, for each fixed $R\in(2/9,1/\pi)$, define

\[
D_R(\varepsilon)=\inf_{E\subset F\text{ a.e.}}
\{P(E)+P(F)-4\pi R^2-2\pi(R-\varepsilon):
 |E|=4\pi R^3/3,
 |F|=\pi(R-\varepsilon)^2\},
\]

where the infimum includes all finite-perimeter pairs. The proposed result is

\[
\lim_{\varepsilon\downarrow0}\frac{D_R(\varepsilon)}{\varepsilon^2}
=\frac{4\pi R}{R+4G_R},\qquad
G_R=R^2-\frac R2\cot\frac1{2R}.
\]

The contribution is this sharp nonlinear minimum asymptotic, including the lower passage from the unrestricted BV class. Constants may depend on $R$. Endpoint uniformity, a dynamical theorem, a multiple-interface extension, and a full functional Gamma-convergence theorem are outside this verdict.

## Why it exceeds a technical corollary

The stipulated profile classifies each separate minimum, but it does not quantify the least cost of making two incompatible optima nest. Here the limiting optimizers have different topology and meet along a circle. At positive epsilon the radius-$R$ ball cannot fit in the separately optimal radius-$R-\varepsilon$ tube. A compactness argument establishes a positive deficit at each fixed epsilon; it does not identify the epsilon-squared law or its coefficient.

Even adding separate squared-asymmetry estimates does not resolve this. I249's missing belt volume is of order epsilon to the power $3/2$. Squaring a forced L1 discrepancy therefore yields an epsilon-cubed lower scale. The required improvement measures the cost of compatible interface displacements along the contact circle, rather than just lost volume.

I263 proposes a concrete route through that obstacle. It replaces an arbitrary pair by an exact paired minimizer; uses a common ambient flow to restore two volumes; and applies perimeter submodularity to intersection/union pairs. The resulting unrestricted scalar comparison inequalities permit classical improved convergence. This is a significant application of familiar machinery, not a new general regularity theorem. Nevertheless, neither separate stability nor ordinary cluster convergence supplies this paired comparison automatically.

The next burden is also mathematical, not merely bookkeeping: obtain graph norms at the epsilon scale with energy-controlled Taylor errors; retain the relative transverse center after translation normalization; derive its O(epsilon) bound from actual inclusion; and pass to a trace obstacle by compactness. A translation Jacobi field then absorbs the first harmonic. Only after these steps does the explicit quadratic calculation govern every finite-perimeter competitor through minimizing replacement.

The coefficient combines the constrained spherical trace capacity and the period-one cylinder resolvent. Its dependence on a periodic Green function reflects deformations away from the contact circle. The sphere cusp and cylinder Green profile are nonsmooth limiting displacements; I253's buffered smooth approximation and exact volumes realize their optimal energy in actual nested sets. Computing a coefficient for a smooth axial ansatz alone would not earn this verdict. The full lower-and-upper nonlinear result does.

## Actual comparisons and the route each leaves unfinished

The detailed primary comparisons and exact source extents are in [literature.md](../sources/i270_nonlinear_contact_contribution/literature.md). Their implications for this gate are:

1. **Pinned family 354, Theorem `intro:main`, and its slice-nesting section.** The profile/equality theorem is assumed true at the required pin. Its quantitative nesting gain is for ordered sections of a single coordinate-monotone CMC minimizer at the cylinder–slab transition. Transporting that operation to two volume-constrained moving interfaces would still require a new paired reduction and a sharp contact-scale expansion. It does not already contain the displayed limit.
2. **AFM 2013, Definition 2.5, Theorem 4.2, Theorem 1.1/Corollary 1.2.** Scalar regularity and stability are fully credited. A possible standard route is selection/replacement, uniform quasiminimality, improved convergence, and second variation. For this task, the substantive missing work in that route is preserving nesting and both volumes while establishing its hypotheses, then identifying the moving contact constraint and optimal energy. Citing AFM alone is insufficient.
3. **Alama–Bronsard–Lu–Wang, Theorem 2.2 and Section 4.4.** The equality of one tension to the sum of the other two already gives the inner/union perimeter formulation. Their later result includes second-order selection of tangent versus concentric shells. In that regime the perimeter-optimal disks can already nest, and the next energy is logarithmic nonlocal interaction. Setting that interaction to zero leaves perimeter degeneracy, not this positive contact cost. Transplanting their method would require new shape compactness and a second-order deformation problem for the sphere/tube obstruction.
4. **Cicalese–Leonardi–Maggi, improved convergence for planar clusters.** Selection and improved convergence are established methods. Their stated cluster theorem concerns the ordinary chamber-sum perimeter and regular triple junctions. Relabeling the present phases produces tensions $1,1,2$; this is a degenerate tension equality with tangent contact. An application needs its own comparison/regularity justification. The read theorem does not bypass I263's bridge.
5. **Lawlor's Euclidean weighted double bubbles; Choksi–Sternberg's periodic phase separation and constrained variations.** These provide weighted-phase and Jacobi/stability precedents. Neither the read Euclidean classification nor the scalar periodic results identify the two-interface obstacle coefficient. Euclidean similarity arguments cannot turn a closed torus tube into an embedded ball, and scalar smooth variation formulas do not regularize an arbitrary nested pair.
6. **Milman's base-induced profile comparison.** This already explains the role of nonnested minimizers in loss of product-profile sharpness. A promising alternative is to slice both sets and solve a coupled BV area-profile problem. The remaining burden is sharp compactness and expansion near the sphere's disappearing pole slices, with contact and singular BV contributions controlled at order epsilon squared. No completed theorem of that form was found in the read section.

These are concrete candidate routes, with their remaining obstacles identified. The verdict does not rest on the absence of a search match or on the length of the proof. Familiar ingredients can yield a substantial result when their combination resolves a previously unpaid constrained limit with a sharp, attained coefficient.

## Repairs to the contribution claim and limits of this verdict

The appropriate nomination is one theorem: **sharp second-order ball–tube nesting cost in the cubic torus for all BV competitors**. Do not nominate I249's linearized minimum, I253's recovery, I263's paired lemma, AFM regularity, or phase-energy rewriting separately. Credit the lattice inequality, smooth volume-fixing variations, classical scalar regularity, translation kernels, second variation, trace compactness, and Green-function minimization explicitly.

Retain the distinction between exact minimizing replacement and regularity of arbitrary near-minimizers. State the result as a limit of minima with a universal lower-sequence comparison; the supplied recovery addresses the optimal profile, not every possible limit displacement. A broad functional Gamma-limit would need additional recovery statements.

The literature citation should identify ABLW's actual **Theorem 4.5**, not the introduction's inconsistent “Theorem 4.21” reference. That is a source-label repair, not an objection to the proposed torus theorem. ABLW's literal containment typo in the shell discussion is likewise not imported as a premise.

The bounded search and reading establish a nonroutine substantial consequence relative to the stipulated source and the specific primary comparisons. They do not establish worldwide priority. Unread literature, general second-order shape-sensitivity results, weighted-cluster contact theory, and recent wetting work could narrow the novelty claim. No such unexamined result is asserted either to contain or to exclude this theorem. Proof correctness remains entirely for the independent correctness gate.

## Artifacts and authentication

- [Contribution analysis](../experiments/i270_nonlinear_contact_contribution/analysis.md).
- [Exact read extents, retrieval limitations and search log](../experiments/i270_nonlinear_contact_contribution/reading-and-failures.md).
- [Input/source/output authentication](../experiments/i270_nonlinear_contact_contribution/input-authentication.json).
- [Primary literature comparisons and fully read retained excerpts](../sources/i270_nonlinear_contact_contribution/literature.md).

All requested I270 work is complete. No subagents, live sibling reads, shared edits, staging, commits, publishing, research programs/tests/scans, or snapshots were used. Detached hashes of the five authored records are returned at handoff; the manifest deliberately does not recursively hash itself.
