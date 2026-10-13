# I246 — independent contribution gate for E4

**Verdict: SUBSTANTIAL.** E4 supplies a substantive complete scalarization result relative to the inspected primary literature. This is a contribution-gate verdict conditional on separate proof acceptance, not a proof-gate conclusion or a worldwide priority certificate. It does not change the supplied count of nine accepted findings.

The exact reviewed artifact is [I242 analytic-attempt.md](../experiments/i242_crouzeix_four_dimensional_rigidity/analytic-attempt.md), SHA-256 **`03c0f05cef564e1bde2630ed725ff755d3bb603ea07dbd39a711e595e96d6627`**, which matches the requested final hash. Full analysis is in [contribution-analysis.md](../experiments/i246_crouzeix_rigidity_contribution/contribution-analysis.md); source scopes and retained primary texts are in [literature.md](../sources/i246_crouzeix_rigidity_contribution/literature.md), with provenance in [input-authentication.json](../experiments/i246_crouzeix_rigidity_contribution/input-authentication.json).

## Claim assessed

For every 1≤n≤4, A∈M_n(C), finite m≥1 and finite-degree P∈M_m(C)[z], set M=max_{W(A)}||P||>0. From ||P[A]||=2M, E4 asserts that W(A) is a nondegenerate disk and that there are unit u,v∈C^m for which p(z)=v*P(z)u satisfies

||p(A)||=2M,   max_{W(A)}|p|=M.

The important assertion is scalar compression of **that same complete polynomial witness**. It is not a claim that P[A] has a reducing nilpotent block. It does not cover nonattained ψ_cb suprema or give a positive-deficit quarter-power modulus.

## Contribution judgment

The credited step is the inverse use of the original positive boundary field. The candidate combines zero complete block slack with X*Y=0 to obtain a totally isotropic range for D=XX*−YY*. At a simple supporting eigenvalue, the positive field has rank d−1. Its isotropic dimension bound is d−max(rank X,rank Y), forcing both coefficient factors to have rank one. The scalar equality theorem becomes applicable only after this step.

This changes what the complete certificate tells us: from nonnegative residuals to a scalar channel inside a specified matrix-valued extremizer. The controlled exterior boundary limit makes that use of support rank meaningful on W(B), rather than on a strictly enclosing domain where equality is not attained. The dimension-four calculation supplies the required arc for each irreducible active block. These operations form a genuine structural bridge.

No separate novelty is awarded to the supplied deficit identity, positive-kernel calculus, Herglotz compactness, inertia bound, scalar disk geometry, finite Schur interpolation, or old anticommuting-matrix algebra. The scalar monomial conclusion and exclusion of larger reducing summands are downstream uses of existing scalar theory. The substantial contribution is their application to force **complete input scalarization**, not the ingredients in isolation.

## Closest prior art and the unfilled step

I read ACV v3 Sections 5, 7 and 11 in full, including their proofs. Section 5 gives finite rectangular extremals and orthogonal Schmidt supports; it does not force ranks one. Section 7 proves scalar/complete equality equivalence only through base dimension three. Its dimension-four reduction retains the (2,2) case. Section 11's scalar polynomial classification is all-dimensional, whereas its complete rigidity conclusions are d≤3. Later inverse-algebra results there are scalar and have additional hypotheses. [ACV v3](https://arxiv.org/html/2608.27346v3).

Jin's ψ is explicitly defined using scalar polynomials. His all-dimensional disk theorem and scalar Schur interpolation do not produce a coefficient compression of an arbitrary P. I read his retained Sections 1–8 and Corollary 1, including proofs, and independently reopened the primary versioned page. [Jin v2](https://www.preprints.org/manuscript/202609.0079/v2).

The stipulated direct and structural companions were checked at the actual theorem and lower-operation level. They supply the complete bound and certificate used here, but do not state E4. The companion's common positive density is for the similar matrix, so its equality fibers alone do not identify original numerical-range geometry. Both pinned raw files matched their immutable Git blobs; upstream truth was not audited.

Thus this is not merely a standard scalar transfer already delivered by the inspected results. The old orthogonality relation permits two mutually orthogonal two-dimensional supports in C^4. The new boundary-rank condition excludes that configuration. Increasing 3 to 4 is not itself the reason for a pass; resolving the surviving two-sided coefficient configuration is.

## Scope and novelty limits

Arbitrary finite coefficient size adds real quantified scope, but old finite-level compression already reduces its apparent infinity. The important reduction is to a one-dimensional coefficient input and output for the original witness. All finite degrees remove the initial quadratic restriction without providing an independent high-degree discovery: the source operations already allow every degree and the rank argument does not use degree two. Polynomial reduction modulo the minimal polynomial preserves evaluation but need not preserve the boundary norm.

The supplied weighted-chain counterexample remains active: at A=[[0,2],[0,0]] and P(z)=[[0,z],[1,0]], P[A] has weights (1,2,1), norm 2, and no scalar-style reducing norm-two nilpotent block. Its scalar compression p(z)=z attains equality. This is consistent with E4 and blocks the naive amplification shortcut.

Targeted searches located no matching dimension-four complete scalarization statement. That is a bounded duplication check, not evidence of worldwide priority by absence. The affirmative verdict rests chiefly on the exact gap in the closest primary results and the structural content of the proposed bridge. The original positive-deficit target, higher base dimensions and nonattained complete equality remain outside this award.

**Disposition:** pass E4 as SUBSTANTIAL at the contribution gate, subject to the separate proof gate. Do not relabel the scalar inputs or supporting technical lemmas as additional findings. No I243/I245 or other live gate output was read. The [reading record](../experiments/i246_crouzeix_rigidity_contribution/reading-and-failures.md) records searches, exclusions and operational limits.
