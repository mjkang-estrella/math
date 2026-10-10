# I29 — common-matroid-base entropy: sharp technical corollary, no count submission

**Disposition:** the proposed inequality is true. A direct use of two existing proof interfaces gives the stronger, rank-sharp bound

\[
 H_{\mathcal C}(x)\ge F(x)-\left(1-\frac1r\right)B(x). \tag{1}
\]

This is **TECHNICAL ONLY** for the present ten-substantial-findings task. The active-normal estimate is already explicit in the stipulated polymatroid source, and the covariance trace argument is already explicit in the stipulated matching entropy source. Their combination needs no new separator invariant. I do not submit a finding, recommend a count increment, claim worldwide priority, or use R011's graph theorem by analogy. The independently attempted gluing route has the concrete compatibility obstruction below; it is not presented as a conditional theorem assuming its missing estimate.

All logarithms are natural; `0 log 0=0`. Let two finite, labelled matroids on E have equal rank r and nonempty common-base family C. Write P=conv{1_A:A∈C}, F(x)=−Σx_i log x_i, B(x)=−Σ(1−x_i)log(1−x_i), and H_C(x)=max{H(μ):μ supported on C, E_μ1_A=x}. Equation (1) holds for **every** x∈P. For r=0 the family is {∅} and all terms vanish; the coefficient in (1) is used only for r≥1. It is optimal among coefficients depending only on r.

## 1. Scope and frozen evidence

The task brief, input SHA256 records, start-of-work Git state, selected pinned source bytes, primary-paper version bytes, query responses, read passages, theorem contracts, and reproducibility scripts are under [the I29 source directory](../sources/i29_common_base_entropy/) and [experiment directory](../experiments/i29_common_base_entropy/). Only those directories and this report are I29 write targets. No agents, shared-index edits, staging, commits, pushes, or other-project writes were used.

The stipulated revision is `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Its proofs are accepted, not audited. The complete 749-manuscript `sources/preprints-tree.json` and read-only 9,340-file I14 corpus/manifest were screened; the truncated root-tree cache was not used. Only selected source bytes were copied. The frozen ledger lagged the user's report that the parent was accepting R011 as the fifth finding. R011's final finding file was not present at the initial read, so the authorized fallback—the full I25 resumed report—was read, together with I25 R2/R3 reviews and the I13 projected-common-base obstruction. No count or ledger interpretation here supersedes the parent.

The two required sources were read through their complete mathematical TeX bodies:

- [Approximate counting of common bases of two matroids](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Approximate-counting-of-common-bases-of-two-matroids-September-23-2026): full `build/main.tex`, including signature, transport, observable variance, trace, evaluation, and counting arguments.
- [An FPRAS for Common Integer Polymatroid Bases with Binary Capacities](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-FPRAS-for-Common-Integer-Polymatroid-Bases-with-Binary-Capacities-October-5-2026): main and every section, especially `polyhedra.tex`, `signatures.tex`, `geometry.tex`, `ports.tex`, `evaluation.tex`, and `counting.tex`.

Relevant proof comparisons also include the matching paper's complete entropy/weighted sections, the cell-bounded table paper's binary and integer signature arguments and transport interface, and the exact-table companion's signature interface. `pinned-manifest.json` distinguishes all retained files from actual read passages in `read-passages.json`; retaining a paper is not represented as reading every auxiliary algorithm in it.

## 2. Primary literature: what was already available

A bounded current primary-paper search was performed early, then refined after the covariance lead. The retained current-version pages and version-specific PDF/text bytes are in `literature/manifest.json`. These are proof-interface comparisons, not an exhaustive priority determination.

**General matroids already have nontrivial all-mean entropy bounds.** Anari–Oveis Gharan–Vinzant, [Log-concave polynomials, entropy, and a deterministic approximation algorithm for counting bases of matroids, v2](https://arxiv.org/abs/1807.00929v2), Theorem 5.2, proves H(μ)≥F(x) when the law's generating polynomial is log-concave. Lemma 5.8 supplies externally tilted single-matroid laws at prescribed means, including limits at boundaries. This does not say common-base laws are log-concave.

More precisely, their Theorem 7.1, stronger than the headline exponential counting factor, implies the following established capacity corollary for general pairs:

\[
 H_C(x)\ge H_{M_1}(x)+H_{M_2}(x)-F(x)-B(x)-L(x)
 \ge F(x)-B(x)-L(x),\quad
 L(x)=\sum_i\log(1+x_i(1-x_i)). \tag{2}
\]

Here H_M is the maximum entropy on all bases of M. To check **both quantifiers**, apply their differential-operator bound to `g_M1(e^θ y) g_M2*(z)` at exponents `(x,1−x)`. The exact factor is
`∏ x_i^{x_i}(1−x_i)^{1−x_i}/(1+x_i(1−x_i))`.
The two capacities have logs `θ·x+H_M1(x)` and `H_M2(x)`. Hence the weighted common-base partition function satisfies the resulting lower bound for every real θ and every feasible x. Taking `inf_θ(log Z_θ−θ·x)=H_C(x)` gives (2), also on faces by finite-support entropy duality. Using the single-matroid entropy theorem on each original matroid gives its second inequality. Their coarser Corollary 7.2 similarly gives H_C≥F−2r and the binary-entropy counting error 3r. Thus merely recovering those bounds would be rediscovery. The stronger first expression in (2) can outperform (1) at particular means; (1) does not dominate every source-specific capacity estimate.

**Stable inputs already yield coefficient one.** Anari–Oveis Gharan, [A generalization of permanent inequalities and applications in counting and optimization, v1](https://arxiv.org/abs/1702.02937v1), Theorem 1.1 and its common-base application, give the sharper coefficient-inner-product capacity factor for multiaffine real-stable inputs. Combining it with single-matroid entropy and the same all-θ dualization gives H_C≥F−B for pairs whose base polynomials satisfy that hypothesis. General matroids must not be silently declared real stable. For partition pairs, Gurvits's [weighted permanent bound, Theorem 2.2, v11](https://arxiv.org/abs/1106.2844v11), directly supplies the weighted Bethe lower bound; its variational form again implies the prescribed-mean inequality. No bipartite specialization here qualifies as new work.

**Capacity improvements retain their hypotheses.** Schweitzer, [Capacity of Lorentzian polynomials, v2](https://arxiv.org/abs/2011.14406v2), Theorem 2.1 and its coefficient corollary, and Brändén–Leake–Pak, [Lower bounds for contingency tables via Lorentzian polynomials, v3](https://arxiv.org/abs/2008.05907v3), Theorems 5.10/5.11, give coefficient/capacity estimates for Lorentzian, denormalized Lorentzian, or stable polynomials. Their proofs reduce to bivariate coefficient estimates and iterate differentiation/specialization. Those closure premises need verification on the polynomial actually used. The four-element example in §5 fails log-concavity for the common-base polynomial, even though both individual matroid polynomials are stable. The source's two positive factorial lifts and their agreement on transversals are not a license to transfer either lift's signature to this polynomial.

**Current counting is much stronger algorithmically, but has different quantifiers.** Chen–Liu, [An FPRAS for Counting Common Bases of Two Matroids, v1](https://arxiv.org/abs/2610.06724v1), Theorems 1.2/1.6, gives common-base FPRAS and weighted log-concave subset-convolution access under its value-oracle, positive-support, and coefficient-range assumptions. Section 2's dual entropy program minimizes a softened-intersection capacity to make complementary pairs sufficiently probable. Its target is agreement of the two views, not an arbitrary prescribed common-base mean. The Poincaré transfer has explicit support/connectivity and curvature hypotheses; it does not prove log-concavity of the hard common-base polynomial. Likewise the stipulated common-base and polymatroid FPRAS sources are not proofs of (1). [The current TU-fiber capacity paper, v1](https://arxiv.org/abs/2609.39917v1), Theorems 1.1/1.4/1.6, concerns specified totally unimodular fibers and its dimension/error factors. Local tight-chain matrices in §3 do not make the entire matroid-intersection inequality system one fixed TU fiber.

## 3. Complete proof of the technical corollary

### 3.1 Exact active-normal rank

The stipulated polymatroid source's `lem:polyhedral-controls` gives integrality and explicitly proves that the tight rank-set normals of one rank system are spanned by a maximal chain. Here is the needed specialization, including its rank accounting.

At x with 0<x_i<1, let T_j={S⊆E:x(S)=r_j(S)}. Submodularity of r_j and modularity of x show that T_j is closed under unions and intersections. It contains ∅ and E. Choose a maximal chain
`∅=A_0⊊A_1⊊...⊊A_k=E` in T_j. Every tight set S is a union of chain differences: if S cuts A_l\A_{l−1} into two nonempty pieces, the tight set `A_{l−1}∪(S∩A_l)` lies strictly between successive chain members. Thus all tight indicator vectors lie in the span of this chain's indicators. Conversely the chain vectors themselves are tight and independent.

Each nonempty difference has positive x-mass and
`x(A_l\A_{l−1})=r_j(A_l)−r_j(A_{l−1})`, a positive integer. Consequently k≤r. The two normal spaces share the nonzero vector 1_E. Their combined rank ρ therefore satisfies

\[
 \rho\le k_1+k_2-1\le2r-1. \tag{3}
\]

The base-polytope intersection equals P by the source's integral-polyhedron statement. At strictly fractional coordinates there are no active coordinate bounds. Hence the minimal face tangent space T is exactly the kernel of these active normals, and

\[
 d=\dim T=n-\rho\ge n-2r+1. \tag{4}
\]

This is valid at every face after coordinate reduction; no graph odd-cut geometry, laminar separator tree, generic-rank assumption, or connectivity assumption is involved.

### 3.2 Entropy regularity and the trace identity

The generic finite-support arguments used in the source matching entropy section apply verbatim to any finite family of indicator vectors. The maximum is attained. H_C is continuous on P: upper semicontinuity follows by compactness of the probability simplex. For lower semicontinuity at x, any sufficiently nearby y∈P can be written `y=(1−t)x+tz`, z∈P, t→0. Indeed a finite inequality description gives a positive uniform extension distance in every feasible unit direction from x using the finitely many inequalities slack at x; active inequalities impose no new obstruction along that ray. Mixing a maximizing law at x with any law at z gives the required limiting lower bound.

At x in the relative interior of its minimal face Q, every realizing law is supported on the vertices of Q. There exists a strictly positive realizing law on those vertices; mixing with such a law and using the singular derivative of entropy at zero shows the maximizer has full support. Lagrange multipliers give
`p_a=exp(θ·a)/Z` on that face. With K=Cov_p(a), one has im K=T, rank K=d, and K_ii=x_i(1−x_i). On T, the mean map has derivative K and is locally invertible. In mean coordinates,
`∇²_T H=−(K|_T)^{-1}`.

Set J_c=F−cB and E_c=J_c−H. At a local maximum along Q, the Hessian on T is negative semidefinite. Its trace after congruence by `(K|_T)^{1/2}` gives

\[
 0\ge d+\operatorname{tr}\!\left(K\,\operatorname{diag}
 [-1/x_i+c/(1-x_i)]\right)
 =d-n+(1+c)r. \tag{5}
\]

Equivalently, use exponential tilt curves with derivatives spanning T. Stationarity cancels acceleration terms because their accelerations also belong to T. This is the source entropy trace argument; it does not assume the common-base generating polynomial is log-concave.

### 3.3 Boundaries and the endpoint coefficient

Fix the original rank R≥1 and ε>0, and set c=1−1/R+ε. If E_c is ever positive, continuity and compactness give a positive global maximum x. Let C_1={i:x_i=1}, C_0={i:x_i=0}. Every realizing basis contains C_1 and avoids C_0. In each matroid contract C_1 and delete C_0. The common bases of the resulting pair are exactly the original common bases with those coordinate requirements, with C_1 removed. The remaining rank is r=R−|C_1|. F, B, and H are unchanged, and every residual feasible mean lifts to an original feasible mean, so x remains a positive global maximum in this residual problem.

If r=0 there are no variable coordinates and the defect is zero, impossible. Otherwise all remaining coordinates are strictly between zero and one. Combining (4) and (5) gives

\[
 0\ge d-n+(1+c)r\ge1+(c-1)r
 =1-r/R+\epsilon r>0,
\]

a contradiction. Therefore E_c≤0 everywhere. Letting ε decrease to zero pointwise proves (1), including equality cases. The strict perturbation is needed: the endpoint trace can be zero on even-cycle faces. This proof neither assumes a favorable maximum on a chosen child face nor makes an induction claim about arbitrary gluing distributions.

### 3.4 Sharpness, weights, and scope guards

For r≥2 take the two partition matroids associated with the two shores of a cycle C_{2r}. Their common bases are exactly its two alternating r-sets A,D, which are disjoint. At mean `p1_A+(1−p)1_D`, 0<p<1, the realizing law is unique and
`H=h_2(p), F=r h_2(p), B=r h_2(p)`.
Consequently `(F−H)/B=1−1/r`. Positive rational activities realize every rational p by changing just one element's activity. Rank one also has exact H=F, so its sharp coefficient is zero. This extremizer is an old bipartite construction, not an independent substantial obstruction.

For any finite real θ, a Gibbs law on C is entropy maximizing at its own mean, by the nonnegativity of relative entropy. Thus (1) applies to **all positive activity Gibbs laws at their own means**, and to all other prescribed means through H_C. The finite variational identity yields

\[
 \log Z_\theta\ge\max_{x\in P}\{\theta\cdot x+F(x)-(1-1/r)B(x)\}. \tag{6}
\]

The universal entropy upper bound here is F+B, not F. If `Q_bin=max_P(θ·x+F+B)`, then B≤r gives
`Q_bin−(2r−1)≤log Z_θ≤Q_bin`.
If `Q_F=max_P(θ·x+F)`, only `log Z_θ≥Q_F−(r−1)` follows. For M_1=M_2=U_{2,4}, the uniform law has H=log6>F=log4, disproving an imported graph upper bound.

Nor does (1) hold for every arbitrary law with mean x: on U_{2,6}, the law uniform on three disjoint bases has H=log3, F=2log3, B=4log(3/2); its rank-two defect is `log3−2log(3/2)=log(4/3)>0`. H_C at that mean is the entropy of the uniform law on all 15 bases. The maximum-entropy/Gibbs qualifier is essential.

Loops in either matroid are absent from all common bases and are deleted. Coloops in either are forced and can be contracted in both; in fact every element forced by the common family can be contracted, whether or not it is a coloop of either individual matroid. All elements retain their labels. Elements parallel in only one matroid cannot be collapsed: in §5, 0 and 1 are parallel in M_1 but have incompatible different completions in M_2. No parallel collapse is used in the proof.

If both matroids split over a common partition of E, the common-base family is a Cartesian product. Entropy subadditivity and independent maximizing laws give exact additivity of H_C; F and B are additive too, so componentwise bounds apply. For unequal original ranks, literal common bases do not exist. Size-k common independent sets, when nonempty, are common bases of the two rank-k truncations. This is a legitimate unequal-rank reduction; it does not establish a variable-cardinality assertion.

## 4. Constructive gluing route and its remaining gap

When S is tight in **both** matroids at x, its ranks agree: r_1(S)=r_2(S)=x(S)=k. The common bases on that face are precisely the Cartesian product of common bases of `M_1|S,M_2|S` and common bases of `M_1/S,M_2/S`. This follows from the usual restriction/contraction basis criterion applied to each matroid. Independent entropy-maximizing laws realize the two means and attain equality in entropy subadditivity. Thus H, F, and B add exactly, with no separator payment.

If S is tight only in M_1, there is still an exact constructive disintegration. Let A=Basis∩S. The interface law π on feasible A has fixed cardinality k but is not specified by the coordinate mean x_S. For each A define C(A) as common bases of the two minors obtained by contracting A and restricting to E\S, retaining only feasible A. Put y_A for the conditional mean on the complement. Then

\[
 H_C(x)=\max_{\pi,(y_A)}\left[H(\pi)+\sum_A\pi_A H_{C(A)}(y_A)\right], \tag{7}
\]

subject to `Σπ_A1_A=x_S`, `Σπ_A y_A=x_{E\S}`, y_A feasible for C(A), and Σπ_A=1. Necessity is the entropy chain rule. Sufficiency is constructive: sample A with law π, then an entropy-maximizing completion from C(A). All unions are valid common bases; compactness handles zero interface masses.

Equation (7) exposes rather than solves the separator problem. The completion matroids depend on the **entire chosen A**. One must choose a jointly feasible compatibility law and control its information cost relative to the nonlinear F/B potentials. Marginals alone cannot supply that choice. I did not obtain a new separator reserve paying all such costs, and do not posit one as a hypothesis of a purported theorem. The successful trace proof makes this unresolved route unnecessary for (1).

## 5. Exact adversarial obstructions

Take E={0,1,2,3}, M_1 partition blocks `{0,1},{2,3}`, M_2 blocks `{0,3},{1,2}`. The common bases are exactly `{0,2}` and `{1,3}`.

1. **Naive tight-flat product:** at x_i=1/2, S={0,1} is a rank-one flat tight in M_1, but r_2(S)=2 and x(S)=1. The two marginal choices on S and its complement are uniform. Their independent product produces an invalid union with probability 1/2. True joint entropy is log2, while the sum of the two marginal entropies is 2log2. The separator must transmit one bit. This is not a graph odd-cut gluing interface.
2. **Common-base log-concavity:** `g=z_0z_2+z_1z_3`. Along the positive local line `(1+t,1−t,1+t,1−t)`, g=2+2t² and `(log g)''(0)=2>0`. Thus hard-intersection log-concavity fails. At uniform activities, covariance has rank one and nonzero eigenvalue one, consistent with the exact trace calculation. Individual partition-polynomial stability has not survived the coefficientwise intersection.
3. **A precise all-root failure:** if a “root” means an entire common basis R and the proposed reserve is `W_R=B−Σ_{i∈R}β(x_i)`, β(t)=−(1−t)log(1−t), no finite universal coefficient c can give F−H≤cW_R for every such root. Put P({0,2})=p, P({1,3})=1−p and root R={1,3}. Then D=F−H=h_2(p), W_R=2β(p), and D/W_R tends to infinity as p↓0. At p=1/102, activities `[1,101,1,1]` realize the law exactly; the rational-log certificate already proves D−W_R>0. This obstruction is specifically to a common-basis root reserve. It does **not** disprove an unspecified rank-one-flat reserve or every possible laminar potential.

These failures also agree with the already recorded I13 issues. Its three-element pair with M_1 blocks `{a},{b,c}`, M_2 blocks `{b},{a,c}` has only common base `{a,b}`, while separately projected visible supports admit c. Its K_{4,4} example has completion masses 14,4,4,2, which fail multiplicative independence (28≠16); product repetition causes the recorded inverse-fiber relative variance `(45/28)^q−1`. I29 does not rebrand those projection failures as a new finding.

## 6. Diagnostics and reproducibility

The deterministic finite screen enumerates all bases of each selected matroid, verifies basis exchange exactly, and forms exact common-base intersections. It covers GF(2)-representable, GF(3)-representable, sparse-paving, partition, mixed representable/paving pairs, and even-cycle extremizers. Positive integer activities induce exact rational Gibbs probabilities; no numerical optimizer supplies a claimed counterexample.

Results: **163 nonempty pairs, 1,274 activity laws, 160 interval-certified entropy checks, and 80 exact active-face rank checks**. Random instances use n=6,…,9 and ranks 2,…,4; cycle tests use ranks 2,…,7. Three generated pairs with empty intersections were excluded and not counted as feasible cases. The geometry checks enumerate tight subsets and compare exact rational row rank with affine dimension on whole and exposed faces, including fixed-coordinate reductions. The finite checks support, but do not prove, the universal theorem.

Certificates use a rational enclosure for log q: reduce q=2^k t, 1≤t<2, set z=(t−1)/(t+1), and sum 36 terms of `2Σ z^{2j+1}/(2j+1)`. The remainder is between zero and `2 z^{73}/(73(1−z²))`; log2 uses the same enclosure and negative k reverses endpoints. Final rounding is outward to denominator 10^30. Entropies use exact rational coefficients. Exact two-disjoint-atom identities certify equality cases rather than misreading an interval crossing zero. Other selected defects have nonpositive certified upper endpoints; the root and arbitrary-law failures have positive certified lower endpoints.

Additional exact diagnostics cover labelled parallels, added loops/coloops, direct products, rank truncation, the false upper bound H≤F, and the false arbitrary-law extension. Source sufficient conditions were checked against the explicit non-log-concave common-base polynomial. No floated optimizer output is a proof artifact.

From the project root:

```sh
PYTHONDONTWRITEBYTECODE=1 python frontier/experiments/i29_common_base_entropy/verify.py --reproduce
```

The verifier checks retained-input SHA256, selected pinned Git blob identities against the full tree, the read-only 9,340-file cache, primary bytes/text, exact retained read passages and source contracts, deterministic diagnostic reproduction, and the artifact seal. Live shared-file/Git drift is reported separately from frozen-artifact validity because other tasks are active. The seal excludes only itself and the mutable verification output. No upstream proof validation is part of this verifier.

The final verification returned **PASS**, with byte-identical reproduction of both diagnostic outputs: 14 frozen inputs, 54 pinned files, 749 inventory manuscripts, 9,340 cache files, 30 retained read passages, 118 source-statement contracts, and 115 sealed artifacts. The live ledger, README, I25 integration record, and Git HEAD/status changed during concurrent parent work; those observations are recorded separately and do not alter the frozen I29 dependencies. The cached-index diff statistic did not change.

The resulting conclusion is a complete sharp entropy corollary and a precise rejected gluing shortcut. Its proof is ready for an independent mathematical check if useful, but it does not clear the requested **independent substantial mechanism** gate. No new substantial finding is submitted.
