# I223 — independent contribution review of sharp Coulomb cost-complexity

**Verdict: TECHNICAL/KNOWN ONLY.** I would retain I220 as a useful quantitative corollary, but would not support its nomination as the remaining substantial contribution after accepting the pinned source. This does **not** mean that I located the fully stated theorem in a previous publication. It means that its remaining bridge is a standard transfer of a known mass-splitting/interpolation mechanism to a geometry whose difficult features are already supplied by the accepted source.

This is an independent contribution judgment, conditional on the proposed theorem being correct. It neither passes nor fails the proof gate, and does not change the accepted count of nine. I did not read I221 or any other active review output, and presume no result from them.

## Object assessed and strongest case for it

I assessed the complete I220 statement, not merely its penalization exponent: for each fixed d >= 2 and s > 0, a particular smooth product-bump marginal on five separated components; lower gaps c(1+V)^(-2) and c(1+S)^(-2/(tp)) for **all** individually preserving pairs, using unweighted central BV variation or the pth fractional energy; matching global recovery by preserving T_n with T_n^3 = Id a.e. and control of the actual square; and a norm-independent obstruction for continuous, W^{1,1}_loc, and finite W^{t,p} maps at tp >= 1. Constants depend on the fixed construction. The upper result does not cover arbitrary smooth bumps. The claims are about comparable constrained infima, not leading coefficients, minimizer existence, or a Gamma-limit.

The strongest positive argument is that one obtains a complete sharp quantitative example in the physically relevant co-motion setting, with exact constraints, where the source gave only nonattainment and equality of values. In particular, a compactness-only positive gap would not imply these rates, generic Borel cyclic approximations need not have any useful BV control, and composition of arbitrary BV maps does not preserve BV. Those are real distinctions. Nevertheless, the supplied construction resolves them using standard tools in a specially chosen product geometry rather than a new substantial principle.

## Exact comparison with the closest paper

[Carioni–Del Grande–Iglesias–Schönberger, arXiv:2609.05062v1](https://arxiv.org/abs/2609.05062v1), Example 4.6, pp. 22–24, considers a uniform line segment transported to two separated parallel segments for squared distance. Its maps double the coordinate on alternating half-cells. It proves cost excess O(N^-2), fractional regularizer O(N^(qt)), and matching penalized scaling epsilon^(2/(2+qt)). Here their q is I220's p, and their fractional order is I220's t. The lower proof first rearranges each branch monotonically, represents the displacement by a primitive of the signed branch indicator, and applies interpolation. It therefore contains both sides of the relevant mechanism, not just a dimensional prediction of the exponent.

Their general results are also pertinent. Proposition 2.1, Proposition 2.3 and Corollary 2.5 give determinism, existence and compactness under an appropriate singular regularizer. Theorem 2.9, pp. 10–13, constructs exact-image maps in charts using matched finite-perimeter partitions, BV transport maps, and separate interior/jump estimates. These are already the ingredients behind the passage from BV to fractional jump-compatible regularity. Propositions 4.1 and 4.4 give zeroth/first-order Gamma-limits under density of finite-energy maps. Crucially, Remark 4.5 explicitly supplies **no quantitative rate** when the first-order limit is identically infinite. Thus it would be incorrect to call the full I220 theorem a direct substitution into a general rate theorem.

The comparison also must not overstate a density obstruction. The elementary identification of their regularizer with an unweighted seminorm uses upper/lower density bounds, and Theorem 2.9 is stated for normalized Hausdorff measures on manifolds. I220's flat bump does not meet those statements verbatim. But their general framework allows Borel kernels: on the positive-density region, a density-compensated kernel can represent an unweighted energy. Flatness is not, by itself, a fundamental exclusion from their abstract setup. Nor do those abstract results then supply I220's sharp rate or exact order-three recovery.

## The actual new bridge and why I judge it technical

The clearest new deduction in this package is the following finite-branch reduction. For a selected branch, write

    S = {x in Q: T_2(x) lies in K_j},
    F = H_j^(-1) composed with T_2 on S,
    beta = F#(nu restricted to S) <= nu/2.

Either a fixed fraction remains in the forbidden central branch, causing a fixed gap, or one such S has mass at least 1/8. The source's local strict convexity turns cost excess into a lower bound for the quadratic displacement E = integral_S |x-F(x)|^2 dnu. This is the exact place where the original qualitative obstruction becomes quantitative.

For phi = eta_r * chi_S, the proposed argument compares

    integral phi d(nu|S-beta) >= m/2 - (3/2)e,
    |integral phi d(nu|S-beta)| <= C sqrt(m E)/r,
    e = integral |phi-chi_S| dnu <= ||f||_infinity C r^sigma P,

where sigma = 1 for BV and sigma = tp for fractional energy. Choosing r of order (1+P)^(-1/sigma) gives the claimed lower powers. The conceptual content is transport dual testing against a smoothed phase indicator, balanced against its interface complexity. The replacement of a signed binary phase by a measure dominated by half the reference measure is useful, but the same test and scale selection work immediately. It does not require controlling derivatives of f or a positive lower bound for f.

This is closely visible in [Seis, arXiv:1309.0556v1](https://arxiv.org/abs/1309.0556v1), Section 3.2, Lemma 2 and its proof, pp. 8–10: split a phase pairing into the error of mollification and a pairing with a transport plan, bound the former by scale times BV, and the latter through transport distance. Seis proves a stronger logarithmic-transport statement in its own periodic binary setting; I am **not** asserting that its theorem literally includes the dominated-measure lemma above. The point is that the specific argument being transferred is established. [Cinti–Otto](https://arxiv.org/abs/1509.01189), Propositions 1.1–1.4, supply further context for interface/negative-norm/Wasserstein interpolation; their exact hypotheses are different and their statements are not invoked as an automatic proof of I220.

On the upper side, the new implementation is a cellwise quantile version of the stripes, completed to cycles:

    v -> Y_k(F_k(v)) -> W_k(F_k(v)) -> v.

The scalar maps are q_l^(-1)(2q_l) or q_l^(-1)(2q_l-1), with the corresponding inverse half-maps. This preserves the conditional probability in each geometric cell; product structure leaves transverse variables unchanged. The construction combines the existing stripe model with the standard equal-mass/inverse-map cyclic gluing in [Colombo–Di Marino](https://cvgmt.sns.it/media/doc/paper/2127/MultiColDim.pdf), Lemma 2.2 and Section 3.1. Their Theorems 1.1/1.4 already establish cyclic approximation for nonatomic identical marginals, including Coulomb cost, but do not bound its BV complexity. I220 makes a quantitatively controlled special choice of those maps.

The rate comes from two familiar calculations: a stationary calibrated residual is quadratic in the displacement inside a cell of diameter O(1/n); O(n) bounded jump interfaces give BV O(n), and the bounded-BV translation inequality with a split at 1/n gives fractional energy O(n^(tp)). The source already allows arbitrary smooth g and already uses conditional CDFs in Lemma 6.2. Choosing g to be a product bump removes transverse quantile regularity difficulties. Completing these one-dimensional monotone rearrangements to three-cycles requires correct bookkeeping, but no new coupled transport equation or cycle-existence theorem.

## Why the stated geometric distinctions do not carry substantial novelty here

* **Singular three-particle Coulomb/Riesz cost.** The accepted source, Lemma 3.1, Proposition 4.1, Lemma 4.2 and Section 7, supplies the collision-free smooth branch geometry, supporting potential, strict convexity and forbidden-pattern separation. On active products the singular cost is a smooth function with bounded derivatives. The transfer does not face a shrinking collision layer. Dimension and Riesz exponent enter its constants through the already accepted local construction.
* **Swapped outer branches.** Fixing the positive outer coordinate is the source's convexity convention. Recovering control of the negative branch by the bi-Lipschitz inverse and a triangle inequality is necessary, not automatic permutation of a Hessian. It is a standard change of coordinates after accepting the source, not new Coulomb geometry.
* **Smooth identical marginals and exact cycles.** Their compatibility with nonattainment is the source's contribution; cyclic approximation is already known. I220 adds explicit regularity control of both powers. The special branch cycle above makes that control a finite list of chart compositions. It is more than mere existence, but remains a standard controlled realization.
* **Flat endpoints and global extensions.** Using only the upper density bound in the lower estimate is sound in scope and useful. Using total variation of monotone quantiles rather than bounding their derivatives avoids flat-endpoint blow-up. Finite-perimeter zero extensions and all support-crossing terms matter for the global statement, but are standard BV/fractional estimates already present in the comparison literature. Setting T(0)=0 to control the actual square off the support is a representative choice, not a new invariant.
* **Sharpness for actual constrained infima.** The all-pairs lower bound and the cyclic recovery do provide the relevant comparison, conditional on their correctness, for large budgets. Reparameterizing n by the variation/fractional budget and optimizing a penalty are elementary consequences. I have not replaced them by a compactness-only claim or a rate for an unconstrained surrogate.
* **Critical tp = 1.** I220's assertion is stronger than saying that its particular stripes have infinite critical energy: every admissible finite-energy map must have a constant component label. The reduction to characteristic functions and local mollifier rigidity at kernel exponent d+1 is a standard Sobolev fact. It gives a useful endpoint corollary here, not a new fractional regularity threshold. The p = 1 inclusion is also an elementary endpoint extension of these estimates, although Carioni et al. formulate q > 1.

[De Pascale–Louet–Santambrogio, arXiv:1407.7022v3](https://arxiv.org/abs/1407.7022v3), Theorem 1.1 and Section 3.2, do **not** directly apply: their polar Lipschitz domains and uniformly positive densities exclude this disconnected target and flat boundary density. Their Theorem 1.2 addresses a different vortex-type epsilon|log epsilon| regime and a finer asymptotic profile. I220 correctly makes no smooth near-optimal recovery claim. Failure of those hypotheses does not itself make the fractional discontinuous transfer substantial.

## Decision and limits

I220 identifies an additional theorem for the accepted source, with concrete value: it quantifies how much oscillation is necessary and shows that imposing exact three-cycles does not worsen the powers. The most creditable extension is the arbitrary-pair dominated-measure lower bound combined with a regularity-controlled cyclic upper construction. My judgment is that these are a standard finite-branch transfer and careful technical completion of known mechanisms, not the substantial new bridge sought by this nomination process.

There is no claim of worldwide duplication or exhaustion of prior art. No outcome of I221 is assumed. The verdict remains a substantiality assessment even if the separate proof review verifies every line. Conversely this report does not certify those lines. No shared record, gate, accepted count, or ancestor file was changed.

Exact reading limits, source locations and input hashes are in the companion literature note and authentication JSON. Output hashes are returned detached. Runtime reports GPT-6.1 Sol with high reasoning; the requested ultrafast service tier is not independently exposed here. No subordinate agents, research code, tests, numerical experiments, repository-wide scans, snapshots, seals, historical replay, staging, commits, or publication were used.
