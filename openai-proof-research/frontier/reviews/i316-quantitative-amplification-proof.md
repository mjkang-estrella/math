# I316 — independent quantitative amplification proof review

**FAIL — exact invalid endpoint step in the frozen proof.** The authenticated input `frontier/iterations/i315-quantitative-amplification-gap.md` has SHA256 `53020ac5aa0e859cf48c3746c92adf2ab832f51dc9bdc7ddaf145bc3d400c41d`. Its section 3, line 96, asserts

    ||h-f||²<= [2+(1+1/sqrt(2))²]epsilon<5epsilon.

Section 3 explicitly fixes d<=r, so epsilon=0 is allowed. For any r>=2 take d=r, Q=P=Phi^T, and the proposal's unit level-r witness x. Then gamma=2, epsilon=0, V=sqrt(2/r)I_r, and h=w=f=sqrt(2/r)Phi. The strict final comparison is therefore **0<0**, which is false. This is a counterexample to an intermediate assertion of the frozen proof, not a counterexample to Q315.

The exact necessary textual repair is to replace the final `<5epsilon` by `<=5epsilon`, or explicitly restrict that strict comparison to epsilon>0. No hypothesis, model, exponent, scope, or numerical constant in Q315 needs to change. This correction is recorded as an actual repair, not concealed as an explanatory expansion; hence the frozen manuscript cannot receive PASS unchanged under a literal entire-proof audit.

**Q315 itself passes the independent mathematical check.** The [full analysis](../experiments/i316_quantitative_amplification_proof/analysis.md) proves the valid weak estimate directly and independently checks every remaining deduction: for every integer r>=2 the specified polynomial-inner model is unitarily irreducible and nilpotent, with

    dim A_r=(r³+3r)/2,    A_r^(r²+1)=0,    w(A_r)<=1,
    C_r(A_r)=2,
    C_d(A_r)<=2-(1-d/r)/22    for every integer 1<=d<r.

C_d is the unrestricted-degree disk-bounded matrix-polynomial supremum with base-first evaluation. The same bound holds for every size-d open-disk Schur function without boundary continuity. The exact new-exponent twirl, both defect kernels, partial isometry, numerical-radius factorization, transpose witness, and irreducibility hold. D=(I-S*S)^(1/2) gives the quadratic defect <=2epsilon; Pythagoras gives the requested weak <=5epsilon estimate and ||W||²>=2-6epsilon. The sign-safe rank comparison gives t(2-6epsilon)<=5epsilon even when the lower bound is negative, and inversion gives the full 1/22 norm gap.

No other invalid step or unpaid mathematical operation was found. The explicit basis, radial compression, spectral loss coefficients, exact unrounded constants, and sign-safe rank comparison are explanatory expansions; only the strict endpoint comparison above requires repair. The parent file was not edited.

Completed I312 evidence was authenticated and read as context, together with its original construction and rank-defect warning. It does not validate Q315's new exponents or constants. The scalar antecedent remains credited to [Gau–Wu (2009), Theorems 5 and 8](https://ir.lib.nycu.edu.tw/server/api/core/bitstreams/761cc49b-4b82-4fd4-8748-960e6473e874/content); exact source scope is in [literature.md](../sources/i316_quantitative_amplification_proof/literature.md). The fixed OpenAI corpus is stipulated true. No contribution, priority, acceptance, or count decision is issued.

[Authentication](../experiments/i316_quantitative_amplification_proof/input-authentication.json) and [reading record](../experiments/i316_quantitative_amplification_proof/reading-and-failures.md) identify inputs and semantic extents. I313 and I314 remained unread. No child agents, numerical scans, git, shared-index edits, or publication were used. Five finalized output hashes are returned detached.
