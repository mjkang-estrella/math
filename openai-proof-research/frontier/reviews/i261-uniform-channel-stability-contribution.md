# I261 contribution review of the authenticated I262 target

**Verdict: TECHNICAL.** This contribution gate does not recommend counting the current theorem as a substantial finding. This is not a proof rejection or a claim that the exact statement is already published. No full proof verdict is issued by this review.

Target: `frontier/iterations/i262-global-channel-stability.md`, SHA256 `1899a85fadb07ed0dd34b1396c31033c80d7a8b88b45455cdcb4f5116931cbfb`. Its complete contents were read and its identity verified. I250 and I259 were read as derivation history. The prepared I259 review was never launched; there is no prior review/rebuttal/repair round to incorporate. All three versions are one prospective finding. The supplied accepted count remains ten toward twenty; this review makes no increment or shared-index edit.

## Exact scope assessed

For each fixed a>0 and 1/2<gamma<3/2, I262 proposes explicit positive constants eta,c_-,c_+, independent of every finite m>=2, such that D(W) is between c_-J(P) and c_+J(P). Here W=w vv^T, w=(r+1)a² sech²(ra x), r=(gamma-1/2)^(-1), phi is the normalized scalar ground state, and J is the weighted squared projector distance to a constant unit channel. The measurable real unit field v must be eta-close in essential supremum to some constant e0. There is no support or derivative restriction. The scalar profile, scale and center are fixed. This is a local transverse stability estimate, not stability for general matrix potentials or the full multisoliton optimizer manifold. Explicit constants are supplied but no optimality for them is claimed.

## Primary overlap assessment

The pinned equality manuscript's `thm:main` gives sharp full-moment inequality and constant-unitary soliton classification. Its fully read action, spectral passage, compactness and rigidity sections do not state D comparable to J. The action theorem `act:quantitative-action` already retains dimension-independent auxiliary first-order and algebraic defects. Turning those auxiliary quantities into a physical orientation metric is not supplied as a corollary there. Its compactness proof uses a factor m in a tail-row estimate, so it cannot simply be called an existing dimension-uniform stability theorem. Its rigidity section already provides the exact supersymmetric factorization used in I262.

The matrix-inequality companion's `thm:main` is decisive: its estimate applies in every finite dimension to arbitrary measurable, noncommuting, positive semidefinite potentials with integrable trace power. Its spectral proof handles all negative eigenvalues by finite-list exhaustion. The action theorem and field, trace and connecting-path statements address the sharp bound and auxiliary construction; the read passages contain no orientation stability corollary.

[Carlen–Frank–Lieb](https://arxiv.org/html/1301.5032v2), Theorems 2.2 and 5.1, are serious prior art for the stability strategy, but do not state this matrix full-sum theorem. [Leng](https://arxiv.org/html/2606.03749), Theorem 1.2, remains a scalar density-distance variant. Replacing W by its norm w loses the orientation completely, since w is unchanged and is already optimal. A formal vector extension via the norm of a wave function also does not by itself pay the extra negative moments: D equals the ground-moment loss minus their sum. Thus these results alone do not justify a KNOWN verdict. [Frank–Gontier–Lewin](https://arxiv.org/pdf/2109.05984), Section 2, concerns scalar finite-rank optimization and qualitative compactness; it is not a dimension-uniform matrix deficit estimate.

## A concrete routine route to the stated conclusion

This assessment is based on a positive derivation, not on failure to find an exact match. Set p=gamma+1/2 and M=||f||_infinity in I262's centered chart. The proposed compression compares every negative eigenvalue after the first with

    K_f = -d² I_(m-1) - U_f,  U_f=B_w w ff^T.

Apply the stipulated matrix companion's main theorem directly at gamma. Rank one gives

    S := sum_(j>=2) |lambda_j(H)|_-^gamma
       <= C_gamma B_w^p integral w^p |f|^(2p)
       <= N_LT M^(2gamma-1) T,
    N_LT = C_gamma B_w^p w0^(1/r)/c²,
    T = integral w phi² |f|²,
    w phi² = c² w0^(-1/r) w^p.

Every hypothesis holds: U_f is bounded, measurable, positive semidefinite and has integrable p-th trace power. The matrix size is m-1>=1, and the source constant has no dimension factor. No spatial support enters. Since 2gamma-1>0, this is already o(T), uniformly over the stated orientations and all finite m.

Keeping the proposed centering, quadratic-form coercivity and isolated-eigenvalue remainder, the lower estimate becomes

    D >= [m_gamma/(2(r+2))
           -m_gamma A0 M² -N_LT M^(2gamma-1)] T.

A different explicit small radius therefore gives the same two-sided conclusion and the same c_-,c_+; details are in analysis.md. This does not establish I262's displayed radius by this alternate route, and it does not replace the independent proof gate for its other steps.

Consequently support-free and dimension-uniform control of the full moment is not a new spectral-estimate mechanism once the stipulated matrix theorem and I262's elementary compressed form comparison are available. It follows by applying the existing theorem to the effective potential, using the soliton weight identity and absorbing a positive power of M.

## Assessment of the proposed synthesis

Principal covariance centering is a useful exact way to identify T=J and remove the constant-rotation mode. The weighted mean error then follows from the chart expansion and Cauchy–Schwarz. Global weighted coercivity is the correct replacement for a nonexistent unweighted threshold gap, but follows by an elementary estimate from the partner factorization already in the equality companion. Dimension uniformity is credible at the mechanism level because only Euclidean operator norms occur; it is not a new feature of the classical matrix trace bound.

The [HLW endpoint theorem](https://www.ma.imperial.ac.uk/~alaptev/Papers/hlw.pdf), Theorem 3.1, and the tailored Hölder interpolation improve the tail bound from M^(2gamma-1)T to M^(4gamma-2)T. I independently read its complete presented proof on rendered PDF pages 3–6; the endpoint input is correctly identified as classical. The improvement is real and the assembly is useful. However, the stated comparability theorem does not require the stronger rate. Neither a sharpness claim nor a consequence separating this rate from routine estimates is established. Counting that interpolation, covariance centering and explicit local perturbation estimates together does not, under the task's substantial-increment gate, elevate this tightly restricted corollary to SUBSTANTIAL.

This judgment takes the strengthened I262 scope seriously: removing L from I259 is a mathematical improvement, and measurable orientations with arbitrary oscillation are covered. The favorable fixed profile supplies both the exact weight identity and an explicit nondegenerate transverse quadratic form. Small essential-supremum amplitude is what permits both remainders to be absorbed. There is no profile deformation, interaction of several occupied channels or arbitrary-amplitude problem left to solve in this statement.

## Issues, possible repairs, and limits

1. Reframe the current result as an explicit local fixed-profile matrix orientation corollary. Credit the pinned sharp theorem, existing soliton factorization and classical spectral endpoint separately. Do not describe full-moment threshold control as unavailable from the pinned inequality.
2. If the stronger threshold rate is intended as the contribution, state it as part of the target, compare it with the direct same-exponent bound above, and establish a meaningful sharpness or new consequence. Merely promoting an intermediate bound to a theorem does not automatically change this verdict.
3. More extensive stability involving profile variations or several active channels could change the assessment, but no such theorem is claimed or proved here. These are possible future scopes, not repair requests or authorized new work.
4. No exact primary duplicate was established in the bounded screen. This is why the verdict is TECHNICAL, not KNOWN. No worldwide priority certificate or exhaustive vector/matrix-stability survey is claimed. Mathematical significance is a judgment; the reproducible reason for this judgment is the concrete alternate closure above.
5. This review does not accept or reject the exact Feshbach constants, form-domain details or original eta. Those remain for the independent proof reviewer. No upstream truth was audited, no sibling review was read, and no numerical evidence was used.

Read extents, retrieval failures, written files and detached hashes are recorded in the assigned experiment files. Source identities are tied to revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; external sources have separately hashed retrieved identities.
