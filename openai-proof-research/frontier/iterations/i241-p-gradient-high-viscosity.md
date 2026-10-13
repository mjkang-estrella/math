# I241 — the high-viscosity branch for actual p-harmonic functions

**Verdict: the high-viscosity obstruction is closed for an admissible nonzero selected sequence; the unrestricted p-gradient convergence theorem is not proved. No acceptance change.**

The completed candidate is an actual-p cylinder estimate. For every n>=2 and m>0 there are constants d_*,k_*,C_*>0, independent of p>=3. Write epsilon=1/(p-2). Suppose u is continuous weakly p-harmonic near a cylinder of axial radius H and transverse radius sqrt(eta)H, and it differs from a linear function of slope P, |P|>=m, by at most eta H there. If eta<=d_* epsilon, set

    L=(H/4)sqrt(eta/epsilon).

On the inscribed epsilon-ellipsoid, of longitudinal radius L and transverse radius sqrt(epsilon)L, the proof constructs actual C² derivatives and obtains

    |D_perp u|<=C_*sqrt(eta),
    |D_parallel u-|P||<=C_*sqrt(epsilon eta),
    ||T_epsilon D²u T_epsilon||<=C_*epsilon/H,

on its half-sized interior. At the center, Du is nonzero. For every lambda<=epsilon and r<=k_*L, its Du-oriented lambda-cylinder has affine error at most C_*epsilon r²/H. No gradient modulus or nonvanishing of Du was assumed.

The exact second normalization produces an explicit polynomial operator that is uniformly elliptic and uniformly smooth near zero jets for all epsilon in [0,1]. Savin's small-perturbation theorem applies because the normalized value error is small. The proof checks its parameter uniformity using the actual quadratic-improvement argument, rather than assuming that local value control already bounds derivatives.

For a selected high-viscosity branch, tau=epsilon/lambda->infinity, strengthen the running maximum so s/lambda^N->0 for every fixed N. At the growing radius H=tau²r it gives a fit with parameter

    eta=kappa lambda,   kappa=64(4tau²)^gamma,   gamma->0.

Hence kappa/tau->0. The domain cost is paid, and concentric fit comparisons retain a positive lower bound on the coarse slope. The theorem then gives fine-scale error divided by lambda r at most C_*/tau->0, contradicting lambda being bad. The wider boxes were never declared uniformly bounded; their growing fit errors were retained.

The full proof is in [analytic-attempt.md](../experiments/i241_p_gradient_high_viscosity/analytic-attempt.md). The missing prerequisite for unrestricted gradient convergence remains deriving uniform qualitative flatness and nonzero microscopic selected slopes for arbitrary actual p-approximants from value convergence and a nonvanishing limiting gradient. The pinned infinity-harmonic lift does not supply it. No uniform C¹ modulus is assumed to hide that gap.

The energy-only route still lacks flux control before derivatives are bounded. The naive limiting equation permits sin(t) with exact fits. An explicit radial family of actual p-solutions also has a nonaffine temporal limit on fixed rescaled boxes; its domain ends before the required growing coarse radius, so it verifies the need for scale information without refuting gradient convergence.

The new candidate is the growing-scale, actual-p exclusion, not Savin's established theorem or a generic reformulation of I236. Its independent contribution remains for review. The full I236 proof was read and authenticated; no tau-uniform conclusion was inferred from it. [Literature](../sources/i241_p_gradient_high_viscosity/literature.md), [reading limits](../experiments/i241_p_gradient_high_viscosity/reading-and-failures.md), and [authentication](../experiments/i241_p_gradient_high_viscosity/input-authentication.json) record the dependencies and scope.
