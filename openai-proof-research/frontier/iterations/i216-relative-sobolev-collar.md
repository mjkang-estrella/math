# I216 — exact boundary follows from the source's smooth cubical cutoff

**Verdict: PROVED SOURCE-DEPENDENT RELATIVE DENSITY; TECHNICAL OVERLAP. NO SUBSTANTIAL NOMINATION.** A stronger linear-cost collar correction remains unresolved. No tenth finding is proposed. The parent owns both independent acceptance gates and the count, presently nine.

For every finite p>3, the assigned target follows from the accepted source operations: every W^{1,p} homeomorphism of the closed unit three-ball fixing its boundary is a strong W^{1,p} limit of diffeomorphisms smooth and nonsingular on the closed ball and fixing that boundary. In fact the constructed diffeomorphisms extend smoothly to R³ and equal identity in a boundary collar. The complete argument and its precise limits are in [analytic-attempt.md](../experiments/i216_relative_sobolev_collar/analytic-attempt.md).

## The missing source operation in I213

The key is **`hp:smooth-cutoff`**, high-range `05-high-preparation.tex`, lines 1945–2046. Given a smooth map close to identity on a cubical band, it produces a locally bi-Lipschitz homeomorphism exactly identity on the inner cube, unchanged near the outer boundary, and with

    ∫shell |DK|^p ≤ C_p ∫nearby band |Dh|^p + ε₀.

This is stronger than the nonstrict `hp:cutoff` followed by qualitative `hp:opening`. Its proof fixes finitely many normalized smooth fillings before using a positive squeeze parameter to suppress their forward energy. `hp:full-rank-correction` already uses this mechanism. These operations are accepted at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, so the resulting localization is paid source overlap.

## Construction and actual derivative estimate

Use I213's paid compression to reduce to F that is already identity outside B_r. Apply ordinary approximation on 2B to get smooth G_j→F. For p>3, convergence is also uniform. A fixed smooth inversion

    J(y)=R ρ̃(y/|y|) y/|y|²

sends the boundary of a cube to a surface lying in any prescribed annulus outside B_r. Here ρ̃ is a smooth positive approximation to 1/||θ||∞. Conjugate G_j by J near that cube. Fill the unused inside smoothly, preserving a collar, and apply `hp:smooth-cutoff`. The uncontrolled energy of this filling is irrelevant: the source estimates only the boundary band, and replaces the whole inside by identity.

Conjugating back gives locally bi-Lipschitz H_j, exactly G_j on a fixed smaller ball and exactly identity outside a fixed larger ball. If η_j is the uniform displacement on a fixed compact annulus and d_j is the W^{1,p} error from identity on the surrounding fixed annulus, the proof obtains

    ||H_j−G_j||_{W^{1,p}(2B)}^p ≤ C(η_j+d_j^p+ε_j).

The shell scale is comparable to η_j. Its volume and the identity's shell energy are O(η_j); the remaining derivative cost is controlled by the annular derivative error. All coordinate constants are fixed before j. No later filling constant multiplies a previously chosen small error.

Analytic §3 proves the required exact-exterior smoothing specialization directly from the fully read source proof: identity lattice data stay exact, support propagation through finitely many patch stages is confined inside a fixed buffer, bad-cube energy is paid after finite library constants are fixed, and the local PL smoothing operations preserve identity outside that buffer. Smoothing H_j in this way yields the required closed-ball diffeomorphisms. The general f follows by the paid compression and a diagonal choice.

**Precision about CS_p:** exact inner and outer matching is proved for the locally bi-Lipschitz H_j. The final smooth maps retain exact outer identity and strong closeness. This report does not claim their exact agreement with G_j on the inner ball. That extra clause is unnecessary for the boundary theorem and has not been silently assumed.

## Second mechanism and stronger unpaid estimate

The distinct ambient-flow route has a precise sufficient estimate. Localize a smooth isotopy's velocity v_t by w_t=χv_t, preserving the protected tracks. If L=∫||Dw_t||∞dt and Q is its integrated W^{1,p} norm over the swept annular region, the localized flow satisfies an error bound C exp((1+3/p)L)Q. Thus exp((1+3/p)L_j)Q_j→0 would pay the correction. The endpoint Sobolev convergence and qualitative isotopy theorems inspected do not give that bound. I213's fixed-scalar-cutoff folding example is respected throughout; it does not refute the corrected construction.

Because full boundary density is source overlap, analytic §6 formulates a stronger target **LD_p**: a smooth correction, exactly fixed on the inner ball and identity outside the outer ball, with error ≤C times the original annular W^{1,p} defect and constants independent of inverse derivatives, minimum Jacobians, and higher derivatives. The source-based proof yields only O(d^{1/p}) from d=||G−id||_{W^{1,p}}, via Morrey and the shell-volume term. Removing that loss requires a defect-energy estimate rather than the source's absolute-energy estimate. Neither LD_p nor a counterexample to it was obtained.

## Prior art and scope

[Primary literature and exact reading limits](../sources/i216_relative_sobolev_collar/literature.md) distinguish planar relative approximation, three/four-dimensional piecewise affine smoothing, and qualitative ambient deformation from the needed derivative estimate. The planar Iwaniec–Kovalev–Onninen theorem already includes compactly supported relative modifications; Campbell–D'Onofrio–Vítek supplies piecewise affine smoothing; Edwards–Kirby provides compact-open deformation, not the claimed flow estimate. No worldwide novelty follows from the bounded searches.

[Reading and failures](../experiments/i216_relative_sobolev_collar/reading-and-failures.md) and [input authentication](../experiments/i216_relative_sobolev_collar/input-authentication.json) record exact sources, scopes and hashes. Existing source copies were read in place. No active I214 or other live-task output was read, and no subordinate agents, research code, numerical/parameter scans, numerical experiments, tests, snapshots, seals, historical replay, shared/ancestor edits, staging, commits, or publication were used. Ordinary retrieval, extraction and provenance hashing only. Detached hashes accompany the handoff.
