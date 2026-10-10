# I93 — final contribution review of I90 Q90

**Conditional contribution verdict: TECHNICAL.** Conditional on I92 accepting the original proof, Q90 is a valid quantitative strengthening worth retaining, but it does not meet this project's requirement of a genuinely nonroutine bridge beyond the stipulated theorems **and their lower proof operations**. The reason is the complete reduction below, not the length of the proof, a failure to find an exact duplicate, or an assertion that generic coresets solve the problem. F already supplies state-indexed continuation records, signed variation accounting, scalar edge tests and the actual metric/color counting. A classical Auerbach envelope and an elementary common-part decomposition of two finite distributions close the remaining step at Q90's full scope.

This is an independent contribution review, **not an original-proof PASS for Q90 or an announcement of I92's result**. I92's in-progress files were neither read nor bound. I90's independent original PASS for I88 A/A′/B is preserved as its existing verdict. There is no repair or reseal of I88 or I90 here. No substantial finding is nominated or counted: eight accepted, two remaining is the supplied state; parent alone integrates.

## Fixed scope and provenance

The immutable corpus revision is `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. All its statements and lower operations are accepted true; their applicability, rather than upstream truth, is at issue. The full I90 report, original I90 brief, this review's complete supplied brief, and finalized I90 parent replay are preserved in the owned source directory. The original I88 brief/report/finalized response remain bound through the unchanged I90 evidence. The I90 seal is SHA-256 `89f356914c26239322fdd3f1bb42dd9a124be0d6867ce65d02e3bf1276813438`; the report is `5d35844a2fd42a6e5d15b756e55e53621b27b433e0bd15236ca0e2f0aab5776c`. The I88 seal remains `a4af4b269cef192734166e228ca2e95d6fd08ee25f03d4163a2fc4de0c9277c6`.

AGENTS and the four informational ledgers were inspected for instructions, current objective and relevant dispositions; their exact frozen bytes are retained. Historical ledgers contain earlier counts, which do not override the supplied current count. Only `README.md`, `frontier/README.md`, `frontier/TEN-FINDINGS.md`, and `frontier/iterations/README.md` may drift. I91 CAT(0) outputs, I92 work in progress, and another unfinished I90 review are not evidence dependencies. No S88/D88 revival or new research lane occurs.

For exact source locations, **F** denotes `preprints/Failure-of-Bounded-Approximation-in-a-Lipschitz-Free-Space-over-a-Uniformly-Discrete-Metric-Space-September-26-2026/`. Its TeX files are reused in `frontier/sources/i14_spectral_width_novelty_r3/corpus/`; its sole PDF representation is reused in I79's `outside/`. The full family has eleven original blobs, including that PDF. Complete used sections and the operative PDF passages were read. `read-manifest.json` pins paths, line ranges, whole-body hashes and passage hashes; `selected-inventory.json` lists every original blob in the four compared families, including representations not claimed as complete reads. There is no unseen alternate F PDF being identified with its TeX by assumption.

## Exact object under review

Fix an **integer** p≥1 and F's construction before selecting T. Set

\[
L=10p,\ R=30p,\ K=10p(R+1),\ D=K+2L+5,
\quad B=4R+D,\quad V=1+4pB,
\]
\[
\Delta\ge4\text{ even},\quad V/\Delta<1/20,
\quad Q=\Delta^{2L+1},\ H=\Delta^{D+1},
\quad k>2\Delta QH,\quad \rho=\Delta QH/k<1/2.
\]

Use the actual block M_p, its anchors A_p including o, full metric d, labels h, and graph sequence G_m. Let N_m=A_p∪⋃_{j≤m}V(G_j), with the **inherited full metric**, X_m=F(N_m), X=F(M_p). For integers n≥2 and m≥1, τ_m(n) is the total variation distance (half the ℓ1 difference) between the empirical induced rooted colored radius-n types of G_m and the independently k-colored Δ-regular tree. Q90 asserts that every real linear T:X_m→X with norm≤2p and maximum anchor error<1 satisfies

\[
 r+1>\frac{k}{4VH}\rho^{-n},\qquad
 r\ge\frac{k}{8VH}\rho^{-n},\quad r=\operatorname{rank}T,
 \qquad\text{if }\tau_m(n)\le1/(40V).
\]

Endomorphisms of X_m are included by isometric inclusion. The original Q88 bounds p≥2, norm≤p/2, anchor error≤1/4 are a subcase. This is exponential in the **observable depth n** with p,Δ,k and the other constants fixed. Neither m nor |G_m| is n; no effective graph-size schedule follows. Ordinary linear rank r, augmented signed-measure dimension d≤r+1, coordinate-support size, envelope mass, net size and nonnegative rank remain different quantities.

## Complete reduction at that scope

The reduction first proves I90's weighted inequality, then uses the classical finite-dimensional ingredient. This order exposes exactly what is and is not supplied by F's printed theorems.

**1. Retain F's metric and signed-measure contracts.** F `blocks.tex`, `lem:block-geometry`, gives separation≥1, diameter≤B, d(x,y)≤1 across source edges, a 1-Lipschitz h, h_i(x)=0 at a vertex of color i, h(a(x))=h(x), d(x,a(x))=R, |B̄(j,2L)|≤Q, and |C_j|≤H for C_j={i:h_i(j)<D}. Closed balls include j. These are bounds in the full metric, so restriction does not increase them. Source incidence reversal distinguishes both orientations of every loop and every parallel edge.

F `reduction.tex`, `prop:coefficients`, gives an onto coefficient identification C:X→ℓ1(M_p\{o}), with
\[
\tfrac12\|c\|_1\le\|\sum c_j\delta_j\|\le B\|c\|_1.
\]
Scalar infimum extension makes X_m→X isometric; no vector-valued extension of T is used. For c_x=C(Tδ_x), set μ_x=c_x off o and μ_x(o)=1−Σc_x. These are actual absolutely summable signed measures on S=M_p (or S=N_m for endomorphisms), not new coordinate states. They obey
\[
\int f\,d\mu_x=(T\delta_x)(f-f(o))+f(o).
\]
F `operators.tex`, `lem:measure-bounds`, supplies the following calculations at exactly the vectors available in X_m. The sign test has Lipschitz constant≤2 even on countable S, and gives ||μ_x||TV≤1+2||Tδ_x||≤V. For b_x(t)=L(1−||h(x)−h(t)||∞/K)_+, the anchor error gives
\[
\int b_x\,d\mu_x\ge L-\frac L K(2pR+1)\ge3L/4.
\]
For a source edge and any 1-Lipschitz f:M_p→[−L,L], cancellation of constants gives |∫f d(μ_x−μ_y)|≤λ=2p. Countable sums converge absolutely. This extends the finite-support calculation by its displayed formula, with no perturbation of T and no support-cardinality assertion.

**2. Apply the source record argument only where its records are finite.** More generally, assume any finite or countable S⊂M_p and measures satisfying the three preceding TV, bump and edge bounds with λ in place of 2p. A pair (x,j) is compatible when ||h(x)−h(j)||∞≤D−4. Its allowed state transitions are **exactly** d(j,j′)≤2L. Mark (x,j) saturated if it starts a length-n matched nonbacktracking walk. At an unsaturated pair every positive matched length is<n; use F's existing r_x(e,j) record and declare only a strict maximizing incidence exceptional. At a saturated pair declare all incidences exceptional.

F `walks.tex`, `lem:exceptional-directions` and `eq:record-inequalities`, already compares a specified pair of states j,j′, not a record with the state index forgotten. If compatible pairs (x,j),(y,j′) are joined by e and an allowed state step, and both are unsaturated, put A_x=max_{g≠e}r_x(g,j) and A_y=max_{f≠ē}r_y(f,j′). Prepending e or ē gives r_x(e,j)≥1+A_y and r_y(ē,j′)≥1+A_x; a zero competing record is handled by the edge alone. A prepended length≥n would make its initial pair saturated, so it cannot occur in this case. If neither direction were exceptional, A_x≥1+A_y≥2+A_x. If either pair is saturated, the endpoint alternative is immediate. Other states at either vertex are irrelevant to this proof. Thus extending the rule from good vertices to unsaturated pairs requires no new continuation principle. This is the precise local refinement, not a claim that F printed pairwise badness.

Write E_e for the exceptional states. F `tests.tex`, `lem:edge-test`, now applies its same prescriptions b_x on S\E_e and −b_y on S\E_ē. Within each set the bump is Lipschitz; across sets distances≥2L dominate the sum of values. At a closer cross pair, positivity of either bump and the h-Lipschitz bound make both endpoint pairs compatible, contradicting the endpoint alternative. Otherwise both values are zero. The data are consistent, including on the intersection. On countable data, inf_j(v(j)+d(j,t)), followed by clipping to [−L,L], gives the same scalar extension; it is finite by boundedness and agrees with the data. Empty data use zero. F's signed error estimate therefore gives
\[
\lambda\ge3L/2-2L\bigl(|\mu_x|(E_e)+|\mu_y|(E_{\bar e})\bigr).
\]

Let B_x be the saturated states and w(x)=|μ_x|(B_x). The **unrounded source sum**, before discarding state information, is
\[
\frac1\Delta\sum_{e\in\mathcal D(x)}|\mu_x|(E_e)
\le\frac{\|\mu_x\|_{TV}}\Delta+(1-1/\Delta)w(x)
\le V/\Delta+w(x).
\]
This follows term by term: an unsaturated state occurs in at most one direction, a saturated one in Δ. Reversal preserves uniform incidences, so averaging gives
\[
\mathbb E_m w\ge\theta:=\frac38-\frac\lambda{4L}-\frac V\Delta.\tag{R1}
\]
F's original `eq:average-error` is the coarser bound obtained by replacing w(x) with V times the whole-root bad indicator. Q90 retains the summands already present in that argument.

**3. Transfer through the common part of the type distributions.** Fix all actual state data, including any operator-dependent S and positive finite envelope ν satisfying |μ_x|≤ν. For each j let F_j(t) be the indicator that a radius-n type admits a nonbacktracking source walk and a state walk starting at j whose colors lie successively in C_{j_s}. Discard only full source-label compatibility, so 1_{j∈B_x}≤F_j(t_x). Labels of a source vertex may depend on radii larger than n; this necessary own-color event avoids importing those labels into the type.

For each fixed initial state, F `lem:rare-walks` counts at most Δ^n source walks and Q^n state sequences. On the tree the n+1 source vertices are distinct, even if states repeat. Thus
\[
\mathbb E_{tr}F_j\le a_n:=(H/k)\rho^n.\tag{R2}
\]
Countable S causes no problem: the n-step neighborhood of a fixed j is finite by Q. For any realized T all of these data are fixed when evaluating a hypothetical colored tree. This is a deterministic comparison of finite distributions, not probabilistic conditioning on T.

Here is a full replacement for the claimed clipping step using only elementary signed arithmetic. Let P(t),P₀(t) be the empirical/tree type probabilities, q(t)=min(P(t),P₀(t)), and τ=Σ_t(P(t)−q(t)). Then τ is the specified total variation distance. For P(t)>0 let W(t) be the average of w(x) over roots of type t; set it to zero for empty types. Put h_ν(t)=Σ_jν(j)F_j(t). We have 0≤W(t)≤V and W(t)≤h_ν(t), although the weights μ_x may vary even between roots with identical types. Consequently
\[
\begin{aligned}
\mathbb E_m w
 &=\sum_tq(t)W(t)+\sum_t(P(t)-q(t))W(t)\\
 &\le\sum_tP_0(t)h_\nu(t)+V\tau\\
 &=\sum_j\nu(j)\mathbb E_{tr}F_j+V\tau
 \le\nu(S)a_n+V\tau.\tag{R3}
\end{aligned}
\]
Nonnegative summation justifies exchanging the countable state sum. Finiteness of ν ensures h_ν is finite. The bounds hold for every P-adapted family, so choosing T after observing the graph costs no union bound over operators. Combining (R1)–(R3) proves exactly I90 W:
\[
\nu(S)a_n+V\tau_m(n)\ge\frac38-\frac\lambda{4L}-\frac V\Delta.\tag{R4}
\]
Equivalently, use g=min(V,h_ν) and the bounded-function TV inequality. The common-part calculation explains why clipping-before-transfer is elementary yet essential: it assigns the unmatched probability mass the already known cost V. Transferring each F_j separately would unnecessarily assign that mass cost ν(S). No positive approximation to μ_x, state sampling, quotient metric, or independence of the operator is assumed.

**4. Classical dimension controls the envelope, not its support.** Let E be a real d-dimensional subspace of ℓ1(S). An Auerbach basis u_1,…,u_d in the ℓ1 norm gives ν_E(j)=Σ_i|u_i(j)|, ν_E(S)=d, and |u(j)|≤||u||1 ν_E(j). For completeness, maximize the determinant of d unit-ball vectors in the finite-dimensional space E; a maximizing tuple is independent, its vectors have norm one, and replacement of the ith column by any unit-ball vector bounds the ith coordinate functional by one. Expanding u proves the inequality. This proof uses compactness of E's ball, not that of the ambient ℓ1 ball, so countably supported vectors are allowed.

Let J₀c=c away from o and J₀c(o)=−Σc. Then
\[
\mu_x\in E=\operatorname{span}\{\mathbf e_o\}+J_0C(TX_m),\qquad d\le r+1.
\]
Here e_o is unit mass in ℓ1, whereas δ_o=0 in the free space. Taking ν=Vν_E dominates all variations and gives ν(S)≤V(r+1). This is exactly classical Auerbach/ℓ1 coordinate-sensitivity domination, already explicit in the retained primary basis literature. It does not require finite supports, positive coefficients, or a nonnegative factorization of T.

For λ=2p, τ≤1/(40V), and V/Δ<1/20, (R4) now yields
\[
V(r+1)(H/k)\rho^n
\ge3/8-1/20-V/\Delta-V\tau>1/4.
\]
Set A_n=kρ^(−n)/(4VH). The fixed parameter inequalities give A_n>ΔQ/(2V)>10Q≥10, whence r>A_n−1≥A_n/2. These are both Q90 conclusions. Without the discrepancy threshold, the same reduction is exactly I90 (15), whenever the stated measure/bump budgets hold. No appeal to F's qualitative infinite-block conclusion, local reflexivity, graph-size scheduling, or asymptotic rank substitution enters.

**5. The finite-cover package is the same reduction.** If μ_x is within TV distance η of one of M centers σ_i of norm≤W, then
w(x)≤η+Σ_i|σ_i|(B_x) and w(x)≤V. Apply step 3 with h(t)=η+Σ_j(Σ_i|σ_i(j)|)F_j(t). Its tree mean is≤η+MWa_n. Thus
\[
\eta+MWa_n+V\tau\ge\theta.
\]
A radius-V ball in a d-dimensional normed space has an η-net of size≤(1+2V/η)^d: disjoint open η/2 balls around a separated set fit in the radius V+η/2 ball, and Lebesgue volume scales as radius^d. This also bounds the greedy packing and yields a maximal finite net with centers in the ball. Taking η=1/16 and d≤r+1 gives M>3kρ^(−n)/(16VH) and the **linear-in-n** rank bound (17). For distance≤ζ to E, nearest points exist in finite-dimensional E by compactness of bounded minimizing sequences. Their norms are≤V+ζ; covering at radius η gives I90 (18) with loss ζ+η and M≤(1+2(V+ζ)/η)^d. These arguments retain diffuse centers on the original S. They are supporting consequences of the same package, not another finding.

## Why this is a technical contribution judgment

The original conclusion is stronger than F's printed qualitative theorem and I88's support estimate. The useful change is real: weighted pair losses and the bounded discrepancy budget connect rank to intrinsic depth. However the source already carries the state index through every record, its proof of the endpoint alternative uses only the two finite records, and its variation average is already a sum over states. Restricting the all-directions rule to the pairs whose records saturate is a local refinement of that same operation. The dimension cost is the classical Auerbach inequality. The adaptive clipping step is the elementary distribution decomposition (R3), valid without changing any geometric data. The reduction above pays all these interfaces and closes every term of the nominated estimate. There is no unresolved new localization lemma hiding in this classification.

It would be insufficient merely to say “standard sensitivity sampling applies.” Such sampling preserves chosen norm/cost objectives, not each original signed integral or the actual metric successor relation. Nothing in the reduction samples. Likewise, replacing S by labels can merge arbitrarily many remote neighborhoods, destroying Q; treating a net of measures as coordinate states does the same. F's anchors are used to supply the bump lower bound, not to justify any of those conversions. I88 A′ remains fully compatible: a diffuse one-dimensional vector has envelope mass one and arbitrarily large support.

Shortness or elementary tools alone are not grounds for rejection. The ground here is the explicit **full-scope reduction to already available local source operations plus classical domination and bounded-measure comparison**. An independent proof acceptance would preserve Q90 as a useful proof-verified technical strengthening. It would not alter the separate contribution judgment.

## Primary and companion comparisons actually made

The complete used proofs, not their abstracts, control these comparisons. Paths, versions and ranges are in the manifests; no external theorem is stipulated merely because it is cited.

- F's complete `operators.tex`, `walks.tex`, `tests.tex`, `blocks.tex`, `reduction.tex` and introduction/reference contracts were read. In the pinned PDF the decisive interfaces are Lemmas 4.1–4.2, 5.1, 5.3, 6.1 and Remark 6.2 (text lines 626–986), matching the TeX operations above. F's finite-support perturbation pays approximation error but no rank-controlled support size. Its abstract criterion is qualitative; the reduction uses its lower operations, not an unsupported application of its theorem at a finite m.
- **C** is `The-cotype-cotype-conjecture-under-the-approximation-property-September-23-2026`. The complete `preliminaries.tex`, `coefficient.tex`, `walsh.tex` and `approximation.tex` operations were read. `lem:walsh-basic` factors a fixed finite-rank operator through a Hilbert space with operator-dependent cost; `thm:uniform-decay` combines that with fixed primal/dual moment hypotheses; `lem:compact-domain` preserves moment lifts through a weighted quotient. The last explicitly notes that coordinate truncations need not descend. The full block here is ℓ1-isomorphic and its dual ℓ∞-isomorphic: the first s unit vectors in ℓ∞ have signed-sum norm one and ℓq sum s^(1/q), so there is no finite uniform dual cotype. Finite X_m have dimension-dependent constants. Binary ranks of Fourier indices are not ordinary operator rank. These operations do not furnish a separate Q90 theorem or invalidate the direct reduction.
- **E** is `Counterexamples-to-the-duality-conjecture-for-metric-entropy-September-24-2026`. Complete `02-matrix-contract.tex` and `03-compression.tex`, including `prop:compression` and `cor:signed-compression`, were read. They compress logarithmic distance profiles using partitions, a common retained index, weighted pivots, and two positive parts. Their replacement guarantee concerns those profiles and enlarged graph radii. It neither preserves F's 2L adjacency nor controls all original signed-measure tests. This is the strongest inspected signed compression companion; it is not being replaced by its headline.
- **U** is `An-explicit-obstruction-to-nuclear-norm-ultrapower-embeddings-September-23-2026`. Complete `nuclear-finiteness.tex` was screened. Its spectral/reduced-density and min/max tensor operations concern representation matches in nuclear C*-algebras, explicitly without a representation-dimension bound. This rank-related hit is unused, not a new lane.
- Dasgupta–Drineas–Harb–Kumar–Mahoney, *Sampling algorithms and coresets for ℓp regression*, retained author-hosted SIAM J. Comput. 38(5) (2009) PDF, §3.1 and Theorem 6 with its complete proof in §3.2. The Auerbach bounded-coordinate calculation provides step 4; row-sampling preserves subspace norms. It does not preserve the free-space state's adjacency or signed bump integrals. The determinant proof above also supplies the exact countable-subspace version needed here. [Primary PDF](https://www.cs.purdue.edu/homes/pdrineas/documents/publications/Drineas_SICOMP_09.pdf).
- Woodruff–Yasuda, *New Subset Selection Algorithms for Low Rank Approximation: Offline and Online*, **arXiv:2304.09217v1**, 18 April 2023. The inspected determinant/Auerbach discussion and scoped §8 sensitivity interfaces concern matrix approximation costs and reweighted rows. Its quoted Lewis-weight and coreset results are not imported into this reduction, and reading those statements is not claimed as independently auditing their cited proofs. The full norm-sampling proof used for comparison is the preceding 2009 primary. [Exact version](https://arxiv.org/abs/2304.09217v1).
- Naor, *Impossibility of almost extension*, retained author-hosted PDF, **Proposition 6, Remark 7 and the entire Proposition 6 proof**: signed zero-mass measures encode Banach-valued almost extension; probability measures impose the additional convex-hull restriction. Its transport-norm pairing does not give a rank envelope or a continuation bound. Its author PDF is pinned by URL/hash, not asserted byte-identical to the separately retained arXiv v2 metadata. [Primary PDF](https://web.math.princeton.edu/~naor/homepage%20files/almost-ext.pdf).
- Ben-David–Childs–Gilyén–Kretschmer–Podder–Wang, retained **arXiv:2006.12760v1**, §6.1.2, **Algorithm 1 and Lemma 58 with its full consistency proof**. Comparing continuation lengths prevents inconsistent parent choices; that algorithm ignores specified loops/double edges. F already supplies the state-indexed incidence adaptation needed here. F's citation to the 2024 publication's Algorithm 6.1/Lemma 6.3 is not substituted for the v1 locators. [Exact version](https://arxiv.org/abs/2006.12760v1).
- Godefroy–Ozawa, *Free Banach spaces and the approximation properties*, **arXiv:1201.0847v2, Proposition 7 and complete proof**. Finite metric pairs with arbitrarily large exact extension norm are obtained from a compact AP obstruction by a diagonal limit. Duality fixes the target range. It neither gives Q90's arbitrary-range rate nor supplies a graph-size schedule. [Exact version](https://arxiv.org/abs/1201.0847v2).
- Johnson–Pisier, *The proportional UAP characterizes weak Hilbert spaces*, retained **arXiv:math/9201220v1**. The definitions of k_X(K,s) and approximation numbers and the complete **Proposition 1.1** perturbation proof were read. That step assumes weak-Hilbert nuclear approximation control and yields bounded-rank maps fixing each s-dimensional subspace. No such uniform geometry is given here. The main classification is not imported or claimed independently audited. [Exact version](https://arxiv.org/abs/math/9201220v1).
- Petrova–Wojtaszczyk, *Lipschitz widths*, retained **arXiv:2111.01341v1**, 2 November 2021, **Proposition 4.4 and Lemma 4.5 with full proofs**, and §5 definitions/Theorem 5.1 proof. The packing argument pays exponential-in-dimension covering size, exactly the sort of cost producing I90's weaker linear rate. Kolmogorov width permits nonlinear choice of nearest points; linear width requires a linear map but no fixed norm cap in that definition. These are comparisons of their stated interfaces; no width theorem is an extra premise of steps 1–5. [Exact version](https://arxiv.org/abs/2111.01341v1).

There is a precise reason ordinary approximation numbers do not already state Q90. For I:X_m→X, a_s(I)=1 when s≤dim X_m: any rank<s map has a nonzero kernel vector on which I−T has norm one, and T=0 gives the matching upper bound. That unit-ball statement has no local anchor accuracy or norm budget. Conversely, the finite anchor set lies in a fixed finite-dimensional span; its Kolmogorov width vanishes once that span is permitted, and a bounded finite-rank projection fixes it if no uniform projection-norm cap is imposed. Thus an anchor-rank obstruction is not an ordinary width lower bound in disguise. This distinction strengthens the need to pay the metric reduction; it does not rescue a substantial verdict after steps 1–5 pay it.

## Search, diagnostics, evidence limits and seal

Four new bounded web-search rounds are retained verbatim, including irrelevant and secondary hits. Only actual primary texts are mathematical comparisons. The early generic searches were noisy; the exact-author searches identified primary versions. Searches did not certify absence of a duplicate, and the technical verdict does not depend on such absence. **No genuinely unresolved source comparison remains necessary to this disposition.** A worldwide bibliography, all cited-paper proofs, and every unrelated search hit have not been exhausted.

Three new discovery searches scanned the exact **10,373 original blob positions** of the I88 augmentation of I79's immutable full map. `sources/preprints-tree.json` has 13,223 entries and 749 manuscripts; the old 719 catalogue and truncated root tree are not the domain. Existing I14 original bodies (9,340, inventoried using `rg --files --no-ignore`) and I79's other 1,033 bodies/776 PDF texts are reused in place. Ordered line multisets preserve duplicate representations. Continuation returned 181 records across 59 manuscripts; domination/sensitivity 534 across 103; widths/rank 88 across 30. Boolean sensitivity and unrelated physical continuation hits are not ℓ1 domination evidence. This is a syntactic full-domain screen, not complete semantic reading of 749 manuscripts or all-PDF re-extraction.

`diagnostics.py` independently enumerates actual bounded matched walks in small permutation multigraphs, checks pair saturation and the sharp degree-four exceptional-variation budget, and tests the endpoint alternative with loops, parallel edges, ties and zero records. Exact finite distribution tests check the common-part estimate with operator-adaptive signed measures, overlapping signed Auerbach vectors, diffuse dimension-one envelopes, and strict parameter budgets. A metric toy example tests degree inflation under label identification; it is a counterexample to an unconstrained conversion, not a new F theorem. These are meaningful finite checks of the reduction's interfaces, not the large actual source graphs or a universal proof. Exact counts are sealed in `diagnostics.json`.

The verifier is offline and read-only. It validates exact I93 owned inventories, immutable references, frozen snapshots, preserved brief/report/parent-response bytes, the unchanged I90 seal and its evidence replay, all original blob identities and inherited search-body hashes through that replay, all three new ordered search multisets, read passages, the four-family inventory, two newly retrieved primary PDF re-extractions, and independent finite diagnostics. The I90 replay additionally re-extracts its six primary PDFs. This is **eight scoped primary PDF replays**, not re-extraction of all 776 corpus PDFs. A hash replay is not a proof. No fetch, repair, rewrite, bytecode cache, or reseal is part of verification.

Run from the repository root:

```
python3 -B frontier/experiments/i93_anchored_rank_approximation_novelty_r3/verify.py
```

Preseal corrections, bounded-search noise and scope exclusions are preserved separately. The single final seal is created only after the preseal checks succeed; its hash is supplied in the final handoff. No owned byte is changed after sealing. Only this report and its two assigned directories were written. No shared edit, child, staging, commit or publishing occurred. The final disposition remains **TECHNICAL conditional on original-proof acceptance by I92**, with no count increment and no worldwide-priority, human peer-review or formal-certification claim.
