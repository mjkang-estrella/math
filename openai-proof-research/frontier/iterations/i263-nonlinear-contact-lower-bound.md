# I263: the nonlinear ball–tube contact lower bound

2026-10-12. **Research proof supplied; no acceptance or contribution verdict, and no count change.** Ten accepted findings toward twenty remain the supplied status. No subordinate agents, live sibling-content reads, shared edits, staging, commits, publication, snapshots, research code, tests or numerical scans were used.

For the exact I249 target, this round supplies

    liminf_{epsilon down to zero} D_R(epsilon)/epsilon^2 >= K(R)

for every fixed R in (2/9,1/pi), with K(R)=4pi R/(R+4G_R) and G_R=R^2-(R/2)cot(1/(2R)). Together with I253's recovery, checked rather than assumed, this yields the claimed full limit. The complete proof is in [analysis.md](../experiments/i263_nonlinear_contact_lower_bound/analysis.md). There is no residual mathematical bridge stated conditionally in that proof. Independent validation of this new full-limit proof and a contribution verdict have not occurred; this report does not preempt them or create a pending delegated task.

The lower bound applies to arbitrary finite-perimeter pairs by exact minimizing replacement. It does not assert that every arbitrary near-minimizer itself has smooth graphs. This distinction handles allowable tentacles and concentrations in original competitors without an unjustified smoothing claim.

## What pays the missing passage

1. The direct method supplies exact paired minimizers at each epsilon, with no larger energy than any proposed finite-perimeter pair. The existing ellipsoid competitor already bounds their total deficit by O(epsilon^2). Stipulated pinned equality classification and L1 compactness put each subsequential limit at a radius-R ball inside a radius-R shortest tube. Projection to the transverse two-torus forces the ball center onto the tube axis. Only common translations and signed coordinate permutations are used as ambient torus isometries.

2. A common ambient flow corrects BOTH volumes while preserving inclusion. Its two volume derivatives are independent: one smooth field has positive flux across a free sphere patch inside the limiting tube; the other has positive flux across a tube patch outside the limiting ball. The derivative matrix is diagonal and invertible at the limit. Volumes are integrals of smooth Jacobians over the measurable sets, so L1 closeness suffices to keep this matrix uniformly invertible. Finite-perimeter sets need no prior clean correction patch or boundary regularity. Correction cost is bounded linearly by the two volume errors.

3. For an unrestricted proposed inner competitor H, use the nested pair (H intersection F,H union F). Perimeter submodularity bounds its energy by P(H)+P(F). Its total pair L1 change is EXACTLY |H triangle E|. Correct both volumes by the common flow and apply exact paired minimality. This proves P(E)<=P(H)+Lambda|H triangle E| uniformly. For an outer competitor H use (E intersection H,E union H). Both interfaces are thus uniform scalar omega-minimizers, including the all-ball quantifier in AFM Definition 2.5. This lemma is proved in full, rather than obtained from separate stability estimates.

4. The precise external theorem is Acerbi–Fusco–Morini Theorem 4.2, final PDF page 22. It turns uniform scalar omega-minimality, bounded perimeter and a smooth L1 limit into global C^{1,alpha}-small normal graphs. All its hypotheses now follow from the preceding paired argument. No equal-tension cluster theorem, CMC-at-contact assertion, W^{2,p} premise, or independent approximation preserving nesting is invoked. The theorem itself is an established external dependency; the relevant statement and definition are fully read and retained.

5. Choose reference centers by the implicit function theorem to remove translation Jacobi modes, retaining the relative transverse center h. Exact-volume graph formulas, with remainders bounded by o(1) times H1 energy, and uniform spectral gaps yield graph H1 norms O(epsilon). Sphere and tube means divided by epsilon converge to zero. Weak H1 compactness, strong L2 compactness and compact equatorial traces give the Jacobi-energy lower limit even in the presence of rescaled energy concentration.

6. Actual nonlinear inclusion at the inner equator gives the exact inequality

       epsilon+h dot e_theta+psi(theta,0)
          <= eta(arg[h+(R+psi(theta,0))e_theta],0).

   Trace estimates force h=O(epsilon). Its angular reparametrization tends to the identity with controlled Jacobian, so the limiting obstacle is v-u>=1+d dot e_theta. Add the spherical translation Jacobi field d dot omega_transverse to u. Its energy is unchanged and the resulting pair has v-u_tilde>=1, exactly the I249 admissible trace constraint.

7. I249's entire quadratic proof was independently checked, including nonnegative discarded angular blocks, the mean-zero spherical cusp, the periodic Green-function mean and derivative jump, and the constrained two-variable minimum. It gives energy at least K(R). I253's strict-buffer smoothing, exact volumes, full inclusion and successive order of limits were checked in full and give the matching upper bound.

## Scope and records

The pinned source theorem is family 354, `paper.tex`, Theorem `intro:main`, at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; upstream truth remains stipulated. Constants depend on fixed R, and no endpoint uniformity or worldwide novelty is asserted. The core-shell equality case in Alama–Bronsard–Lu–Wang already recognizes the sum-of-two-perimeters structure; that algebra and the general concept of nested phases are not claimed as novel. Its planar Euclidean core-shell minimizers and nonlocal droplet regime do not prove this fixed-radius torus ball–tube contact coefficient. Read extents and bounded search limits are in [reading-and-failures.md](../experiments/i263_nonlinear_contact_lower_bound/reading-and-failures.md) and [literature.md](../sources/i263_nonlinear_contact_lower_bound/literature.md).

The required original I249 analytic note was read completely and its SHA256 is exactly `ef588588ace48958cc6f3fad4af84d01c52198ea4bff10a1e3a890cd86772413`. Full I249 disposition, final report, authentication/reading records and I253 were read. Initial filename discovery listed unrelated filenames but no live sibling file content was opened.

[Input authentication](../experiments/i263_nonlinear_contact_lower_bound/input-authentication.json) records retained primary bytes, source URLs, exact extents, relevant local-input hashes and authored-output hashes. Its own hash is detached at handoff to avoid recursion. All requested work in this research round is complete; no child run or requested computation remains pending.
