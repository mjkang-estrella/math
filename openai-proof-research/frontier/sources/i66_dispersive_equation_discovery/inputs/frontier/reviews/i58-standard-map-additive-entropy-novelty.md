# I58 — independent contribution audit of I54 additive standard-map entropy

2026-10-09 (America/Los_Angeles; primary retrievals dated in UTC). **Verdict: TECHNICAL ONLY.** The original-proof condition is now satisfied: the completed [I57 audit](i57-standard-map-additive-entropy-r2.md) gives H/SC, G and their supporting claims **PASS ORIGINAL WITHOUT REPAIRS** under the stipulated premises. This contribution decision was derived independently before that dependency update and is unchanged by it. H is a useful stronger consequence of the accepted proof, but its indispensable amplification mechanism is already in that proof and was already extracted in I52’s S. I54 supplies an elementary quantitative seed and a relative crossing. G is a separate, restricted technical consequence of the accepted graph machinery; it does not independently qualify as substantial. No exact published duplicate, new correctness failure, acceptance, worldwide priority, or count increment is asserted.

The judgment is relative to **all theorem statements and proof operations** in `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, accepted as true by instruction. It is not relative just to the source’s positivity theorem. I57 independently owns original-proof correctness. After the user supplied its completion, I read its complete review and verifier and froze them; I did not poll the task. Its analytic PASS is distinguished from evidence reproduction and from this contribution judgment. H53/I55/I56 are unrelated.

**1. Exact object being assessed.** Put

\[
f_k(x,y)=(x+y+k\sin(2\pi x),y+k\sin(2\pi x))\pmod1,
\quad K=2\pi k,\quad M=K+4,\quad \ell=\log M.
\]

H asks for absolute finite constants \(C,K_0\) such that normalized-area entropy satisfies
\[
h_m(f_{K/(2\pi)})\ge\log(K/2)-C\qquad\text{for every real }K\ge K_0.
\]
There is no noise, map perturbation, discarded parameter set, ergodicity assumption, or expansion at every point. The constants in I54 are existential. H does not prove the exact lower bound \(\log(K/2)\), a vanishing additive error, or the explicit remainder conjectured by Knill.

I read the complete I54 and I52 reports, their original briefs and objections, current status ledgers, and all seven mathematical sections of the actual standard-map source, including the local-scarcity proof, finite graph construction, selected-scale measure construction, shape classification, and capped endgame. The complete tree and ignored corpus search identify one standard-map master and no separate additive-entropy companion. This absence alone is not a contribution argument. Inputs, direct pinned files and exact passage ranges are retained in the [I58 evidence](../sources/i58_standard_map_additive_entropy_novelty/).

**2. Independent quantitative-seed/relative-crossing reduction.** The following argument gives the concrete reduction underlying the verdict. It does not infer an entropy lower bound directly from finite-time lower bounds.

In the area-preserving coordinates \((q,p)=(x,x-y)\), the transfer matrix is
\[
A(q)=\begin{pmatrix}2+K\cos(2\pi q)&-1\\1&0\end{pmatrix}.
\]
Let \(a_n=n^{-1}\int\log\|T_{0,n}\|\,dm\), \(e_n=1-a_n/\ell\), and \(d=1-h/\ell\). Determinant one gives \(0\le e_n,d\le1\). Stationarity, subadditivity, and the stipulated Oseledets/Pesin interface give \(e_{2^jn}\uparrow d\) for every fixed positive integer \(n\). The source’s `scale:doubling` gives, uniformly at sufficiently large K,
\[
e_n\le e_{2n}\le D e_n+D/n
\tag{D}
\]
for one absolute \(D\ge1\).

Write SC for the source’s postselection impossibility: no parameter sequence \(K_j\to\infty\) has dyadic \(n_0<N\), \(\epsilon=e_N>0\), satisfying
\[
n_0\to\infty,\quad\epsilon\to0,\quad\epsilon n_0\to\infty,
\qquad e_{2^mn_0}=o(\epsilon),\quad e_{2^mN}=O_m(\epsilon)
\tag{SC-data}
\]
for every fixed integer m. Negative shifts are used only when integral. SC is an extracted proof interface, **not an external axiom**; its source applicability is detailed in paragraph 3.

Here is a general consequence, with all scalar hypotheses exposed. For any prescribed dyadic schedule \(n_0(K)\to\infty\), set
\[
u(K)=e_{n_0}(K)+n_0(K)^{-1}.
\]
If \(u\to0\), then (D) and SC imply \(d=O(u)\) along that schedule. Suppose instead that \(d/u\to\infty\) on a sequence tending to infinity. Choose
\[
\theta=\sqrt{du}.
\]
Then \(u/\theta=\theta/d=\sqrt{u/d}\to0\), \(\theta\le\sqrt u\to0\), and
\[
\theta n_0=\sqrt{d/u}\,u n_0\ge\sqrt{d/u}\to\infty.
\]
For large j, \(e_{n_0}<\theta<d\). Dyadic convergence therefore produces a first crossing \(N>n_0\) with \(e_N>\theta\). Its predecessor and (D) give
\[
\theta<\epsilon=e_N\le D\theta+2D/N\le D\theta+D/n_0=O(\theta).
\]
Thus \(\epsilon\to0\) and \(\epsilon n_0\to\infty\). For fixed \(m\ge0\), iterating (D) yields
\[
e_{2^mn_0}\le D_m u=o(\epsilon),
\qquad e_{2^mN}\le D_m(\epsilon+N^{-1})=O_m(\epsilon).
\]
Negative shifts follow from dyadic monotonicity. These are SC-data, a contradiction. In particular \(N/n_0\to\infty\): otherwise some fixed shift of the seed would already exceed \(\epsilon\), contradicting its negligible normalized deficit. No observation threshold in the bridge theorem has been changed.

Now pay the seed. I52 F states, for \(K\ge16\), \(2\le b\le K/4\), all \(n\ge1\),
\[
a_n\ge\log(K/2)-2nb\ell/K-2/[b(b-1)].
\tag{F}
\]
Its ingredients are elementary and parameter-uniform: the uniform one-time q-marginal bounds the bad strip by \(2b/K\); a union bound costs \(2nb/K\); the recurrence started at \((1,0)\) has successive absolute ratios at least \(b-1\) on the good orbit; and the circle identity \(\int\log|2+K\cos(2\pi q)|dq=\log(K/2)\) follows by factoring the quadratic with both roots on the unit circle. The signed scalar-log contribution removed on the bad set is bounded **above** by \(n\ell\); no sign error or independence hypothesis is needed. This confirms the finite estimate used here within its original scope.

For I54’s actual choices
\[
n_0=2^{\lfloor\log_2K^{1/4}\rfloor},\qquad b=K^{1/8},
\]
(F) gives an additive error at most
\[
R_K=2K^{-5/8}\ell+4K^{-1/4}=o(1).
\]
Consequently
\[
e_{n_0}\le[\log(2+8/K)+R_K]/\ell=O(\ell^{-1}),
\qquad n_0^{-1}=o(\ell^{-1}).
\]
The abstract reduction gives \(d=O(\ell^{-1})\), hence \(\ell-h=O(1)\), which proves H with absolute existential constants. These constants are absolute because the schedule, sine map, and all source constants are fixed; the abstract statement does not promise one constant uniform over arbitrary unrelated schedules or systems.

Equivalently, using exactly I54’s normalization, if \(B=\ell-h\to\infty\), take \(\theta=\sqrt B/\ell\). Since \(0\le B\le\ell\), \(\theta\le\ell^{-1/2}\to0\), \(d/\theta=\sqrt B\to\infty\), \((e_{n_0}+n_0^{-1})/\theta=O(B^{-1/2})\), and \(\theta n_0\to\infty\). The same first crossing supplies SC-data. Negation of the uniform existential C,K₀ statement supplies such a sequence; bounded K cannot create unbounded B because \(B\le\log(K+4)\).

An independent simplification shows how little quantitative initialization is required: one may instead take **b=2** and dyadic \(n_0\asymp\ell^2\). Then (F) gives
\[
a_{n_0}\ge\log(K/2)-1-O(\ell^3/K),\quad e_{n_0}=O(\ell^{-1}),
\quad n_0^{-1}=O(\ell^{-2}).
\]
The same argument proves H. The growing power horizon and the vanishing additive finite-time error are therefore not indispensable innovations. This is an alternative reduction for assessing contribution, not a repair to I54.

**3. Where SC is already present, and why its extraction is technical.** The opening assumption in `scales.tex` is zero exponent almost everywhere along a parameter sequence. Its direct consequence `scale:long-deficit` is \(e_n\to1\), used to guarantee that the chosen threshold is eventually crossed. The following downstream operations use the displayed selection data instead:

- `scale:local-mass` telescopes \(J(I)\) to differences of endpoint deficits and bounds the squared half-deficit difference \(V(I)\) by another telescope. Fixed shifted initial deficits vanish after division by \(\epsilon\); terminal shifted deficits remain bounded. No rate of convergence to 1 is used.
- `scale:limits` uses the finite test cover, compact distance arrays, integer alignment and those local masses. `scale:decomposition` uses the exact identity \(Sg_n=g_{2n}\), the negligible initial measure and positivity to obtain \(S_*\mu=\mu+\nu\) and \(\mu=\mu_\infty+\sum_{j\ge1}(S^{-j})_*\nu\).
- `shape:exclusions` divides fixed cancellation bounds by \(\epsilon\); the exponential error disappears because \(\epsilon n_0\to\infty\). Its weighted bridge estimate uses \(W=J+V\), one fixed shortfall H, and a **fixed** threshold \(\eta>0\). A safe observation bound is \((R,L,B)=(3,6,2)\) for W, with H bounded by \((1,1,1)\). The fast-bridge event remains. Constants may depend on the chosen fixed intervals and \(\eta\); these are not the moving scalar crossing threshold \(\theta\).
- `end:balance` obtains \(\int G\,d\mu=H_\Phi>0\). Slow affine speeds are removed by flatness of the fixed cap. Each intermediate affine speed is covered by a fixed rational threshold. At unit speed the truncation error is \(O((\epsilon n_0)^{-1})\), and the proof first takes the fixed weak limit, then sends a dyadic interval size to zero. There is no need for a test family whose complexity grows with K.
- `end:terminal` uses translation invariance and nonempty slow interiors in the already classified limit shapes. If \(\nu\ne0\), it loses a strictly positive amount for that one limit; if \(\nu=0\), its contribution is zero while \(H_\Phi>0\). `end:remainder` uses the existing translation/dilation decomposition and yields a nonpositive remainder. These contradict the same exact balance.

The scarce-cancellation and bridge proofs were also read, not treated as positivity black boxes. Their fixed constants and threshold contracts are precisely what the above reuse needs. The local-scarcity compactness does not need a newly computed quantitative modulus. Its difficult reciprocal-cosine degeneracies and the source’s affine-mass retention remain the source’s contributions.

I52 S already explicitly stated that the downstream construction uses only these selected-scale properties, and already replaced the zero-exponent crossing justification by a positive eventual deficit. I54 removes the need for that deficit to be bounded away from zero, by crossing between a quantitative seed and a hypothetically much larger terminal deficit. The square-root interpolation in paragraph 2 pays this change without modifying any downstream lemma. Re-exposing the interface is useful, but not an indispensable new mechanism beyond I52 plus the accepted source operations. This is why the contribution verdict is technical even if H passes as a correct, striking quantitative theorem.

I52 correctly left H open in its own report: S as a bare conclusion has no rate, and a \(\sqrt{\log K}\) additive loss is compatible with that conclusion. Its failed attempt to sum the crude cancellation bound is still failed; its conditional-density premise is still unpaid. I54 legitimately changes the route. The objection here is not that it silently assumes either old missing premise, but that its successful claimed route is an elementary amplification corollary of the machinery already available.

**4. Independent assessment of G, with its restricted quantifiers.** For all sufficiently large K, fix \(c=49/50\), and let
\[
E_B=\{z:\|T_{0,-l}(z)\|\ge M^{cl}\text{ for }1\le l\le B\},
\qquad E_\infty=\bigcap_{B\ge2}E_B.
\]
These are restrictions of area, not normalized conditional probabilities; they need not be invariant. I54 G selects one of two backward Dirichlet row kernels on each finite-prefix eligible set. Its constants are asserted uniform in B, time origin, and sufficiently large K. On the regular part of E∞ the limiting section is the unstable line. It claims, for all \(s>0\),
\[
m(E_B\cap\{|v-r_B|<s\})\le C\min(1,s/K),\qquad
m(E_\infty\cap\{|v-r^u|<s\})\le C\min(1,s/K).
\]
It also claims the restricted logarithmic tail \(\int_{X>T}X\le C(T+1)e^{-T}\), where \(X=\log^+(K/|v-r|)\), uniformly in B and K. This is a meaningful finite-to-infinite restricted estimate; it is not just a conditional criterion. Nevertheless its proof has the following direct reduction.

The accepted `bridge:graphs` supplies the extended backward leaf \(p=P(q)\), two closed eligible row choices, all the varied derivative bounds \(|U_a|\le CM^{-4(a+1)/5}\), invertibility of the varied Dirichlet matrix D, and its actual Green inverse with \(G_{0a}=U_a\). The boundary data are \(U_{-1}=1,U_j=0\). Differentiating \(DU=e_0\) along the leaf gives
\[
DU'=-\operatorname{diag}(\phi''(\widetilde q_a)U_a)U,
\qquad
P''=U'_0=-\sum_{a<j}\phi''(\widetilde q_a)U_a^3.
\]
Since \(|\phi''|\le CM\), a geometric series gives \(|P''|\le CM^{-7/5}\), independently of j. This is the elementary inverse derivative \((D^{-1})'=-D^{-1}D'D^{-1}\). The source already uses differentiation of this varied Green problem for transverse determinant distortion and, in `local-scarcity.tex`, differentiates inverse chains through order four. The cubic curvature contraction changes which entry is estimated; it does not create a new regularity construction.

For a fixed row choice, use the source’s fixed grid and label a leaf by its p-intercept t at a fixed q-coordinate. The source’s `bridge:label-jacobian` and regular-level continuation give \(p=Y(t,q)\) with \(0<c_1\le|Y_t|\le C_1\) on the eligible label family. Labels occupy a bounded interval, different leaves do not intersect, and the source supplies smooth local extensions and disjoint Borel chart partitions even when the eligible set has empty interior. Thus integration uses the actual area Jacobian \(|Y_t|\), not unproved conditional density at fixed slope.

For \(0<s\le K/4\), small slope forces any point with \(|v(q)-Y_q(t,q)|<s\) into \(|\cos(2\pi q)|\le1/2\), for large K. On the two fixed arcs, \(|v'|\ge\pi\sqrt3K\); the curvature bound keeps \(v-Y_q\) strictly monotone with derivative magnitude at least K. Each arc has sublevel length at most \(2s/K\). Integrate against the bounded label Jacobian and sum the fixed grid and two row choices. For \(s>K/4\), the trivial area bound suffices after enlarging C. This pays the whole restricted coarea step by elementary one-dimensional monotonicity.

`bridge:direction-step` gives the summable angular error
\[
\sum_{l\ge B}M/(D_lD_{l+1})\le CM^{1-c-2cB}.
\]
The source’s row-kernel error is \(O(D_B^{-2})\). Swap the coordinates back and use small slopes to turn angle error into slope error. Oseledets identifies the inverse-contracting limit with the unstable direction on E∞, since its backward exponent is at least \(c\ell\). Decreasing-set convergence removes \(E_B\setminus E_\infty\); enlarging s by the uniform tangent error passes the small-ball estimate to the limit. Layer cake gives the stated logarithmic tail, including the boundary term \(T\Pr(X>T)\). This is ordinary dominated truncation after a proved restricted sublevel estimate, not unrestricted projective smoothing.

Finally the source’s `setup:shortfall-count` already provides the mass mechanism. At fixed K and fixed L, a norm-realizing vector on a length-N interval has total shortfall \(Ne_N\) in expectation. Every endpoint whose backward L-prefix test fails is counted by the source estimate, giving
\[
(N-L+1)m(E_L^c)\le 4Ne_N/(1-c).
\]
First \(N\to\infty\), then \(L\to\infty\), gives \(m(E_\infty^c)\le\min(1,200d)\). This is an all-prefix occurrence bound, not a return-time tail. Before H it gives only o(1) using S. The projective lower integral then has the schematic form
\[
h\ge(1-\alpha_K)\log K-C-\alpha_K\ell,\quad \alpha_K\le200d.
\]
Writing \(B=\ell-h\) yields only \(B\le O(1)+400B\), up to harmless bounded terms; it cannot force B to be bounded. After H, \(\alpha_K=O(1/\ell)\). That conclusion uses H and cannot be counted as an independent second closure.

G therefore adds a useful estimate in a domain whose uniform geometry the source has already constructed. The remaining operations—one inverse derivative, fixed-arc coarea, a summable tangent limit, and the inherited shortfall count—are routine relative to those exceptionally strong premises. I do not dismiss it merely because it is an intermediate result. Its proof actually reduces to the supplied geometry, and its payoff retains the same eligible-set boundary. Full invariant small-ball/logarithmic control on E∞ᶜ, uniform return-time tails, and a second independent proof of H remain unproved. Their potential significance cannot be credited to G.

**5. Current primary-literature comparison.** Fresh primary response bodies, version pages, PDFs and text extractions are retained; all 22 direct HTTP requests in this audit succeeded. No successful request replaces an omitted failure. Two local evidence-preparation errors are documented separately below. The live arXiv pages show Knill v2; BXY v1; Blumenthal v1; Duarte–Klein AP v1 and continuity v2; Buzzi–Crovisier–Sarig v1; Bloor–Luzzatto v1; Holland–Luzzatto v1. These are the observed arXiv versions, not assertions about identity with final journal typesetting.

- **Knill:** math/9908014v2 opens by withdrawing incorrect parts of the earlier announcement. Conjecture 1.1 proposes \(\log(|\lambda|/2)-[\operatorname{arcsinh}(1/\lambda)+\log(2/\sqrt3)]\). Rescaling its 2π-periodic map gives \(\lambda=K\). Its p. 2 upper bound is compatible with I52 U, but the lower claim is conjectural. H does not reproduce its explicit remainder. The author’s 7–8 October 2026 response distinguishes large-parameter positivity from the exact \(\log(K/2)\) conjecture; this is current status commentary, not proof evidence. [Versioned primary](https://arxiv.org/abs/math/9908014v2); [author response](https://www.quantumcalculus.org/positive-entropy-for-standard-map-by-open-ai/).
- **Blumenthal–Xue–Young:** Theorems 1–3 and Corollary 4 concern iid random shifts and give \(\lambda_1^\varepsilon\ge\alpha\log L\), for fixed \(\alpha,\beta\in(0,1)\), with \(\varepsilon\ge L^{-C L^{1-\beta}}>0\), or \(\varepsilon\ge L^{-C L^{2-\beta}}>0\) under H3. In their standard-map normalization \(K=2\pi L\). Lemmas 7–10 use a three-noise-variable transition Jacobian and a stationary-law concentration estimate with an \(\varepsilon^{-3}\) cost. Proposition 11 balances this against finite good-orbit growth. These actual proof operations do not survive setting \(\varepsilon=0\) at fixed L. Nor can a parameter-dependent \(\alpha\uparrow1\) be substituted without paying its constants. The projective good/bad strategy is an antecedent, not a deterministic H theorem. [Primary](https://arxiv.org/abs/1701.07583v1).
- **Blumenthal:** Theorem D gives a fixed-parameter correlation error \(C\|\varphi\|_\alpha\|\psi\|_\alpha nL^{-\alpha/(3\alpha+4)}\) for \(n\ge2\). The proof specializes Proposition 3.4 to equal coefficients; its error deteriorates with n. Theorems A–C use genuinely increasing coefficients with growth or summability assumptions. Neither supplies an infinite-time fixed-K area-entropy estimate or tangent renewal law. [Primary](https://arxiv.org/abs/1710.09058v1).
- **Duarte–Klein:** AP Theorem 4.1/Proposition 4.2 requires singular gaps and consecutive-product noncancellation; its error is \(O(n\kappa/\varepsilon^2)\). The continuity theorem’s Theorem 1.1 requires a fixed ergodic base, compatible observables, base LDT, uniform Lp bounds and uniform fiber LDT at a spectral gap. Definitions 1.5–1.7 distinguish ordinary and locally uniform LDT. The proofs propagate finite-scale control using these supplied assumptions. Rare visits to a critical strip and source fast-bridge inequalities do not pay them. These are not alternate free quantitative inputs for H. [AP](https://arxiv.org/abs/1507.02967v1); [continuity](https://arxiv.org/abs/1410.0699v2); [authors’ survey](https://silviusklein.github.io/research/DK-survey16.pdf).
- **Buzzi–Crovisier–Sarig:** Theorem A/Corollary 1.1 compare exponent and entropy discontinuity ratios for smoothly converging maps and appropriate ergodic measure limits; the corollary assumes positive limiting entropy and entropy convergence. The more general Theorem D still requires bounded smooth-map convergence and constructs a decomposition through neutral blocks. Large K has unbounded derivative norms and supplies no such map limit; area is not assumed ergodic here. These results do not give a numerical additive deficit bound from positivity. [Primary](https://arxiv.org/abs/2103.02400v1).
- **Deterministic geometry:** Bloor–Luzzatto’s Theorems 1–3 study finite-time foliations, tangencies and expansion outside critical strips; their hyperbolic structure requires an orbit segment to remain in the region. Holland–Luzzatto’s Main Theorem obtains a stable curve under neighborhood derivative, summability and domain conditions, not merely an unspecified positive exponent. Both are explicitly acknowledged in the pinned source. Neither was found to state G with its all-prefix area quantifiers. Their lack of an exact duplicate does not make I54’s derivative of the already accepted Dirichlet graph operation substantial. [Bloor–Luzzatto](https://arxiv.org/abs/0810.3122v1); [Holland–Luzzatto](https://arxiv.org/abs/math/0502236v1).

The [MathDB problem](https://mathdb.com/p/345911/sinais-positive-entropy-conjecture-for-the-standard-map) identifies the positive-area entropy problem. No numerical significance score was observed or inferred. Topological entropy, entropy of a maximizing measure, full Hausdorff dimension of a hyperbolic set, nearby conservative perturbations, and changing-coefficient or noisy systems do not match H’s quantifiers. The bounded search establishes no exact full-scope external duplicate. **TECHNICAL ONLY, rather than DUPLICATE**, is justified by the explicit reduction above, not by a claimed literature theorem already proving H.

**6. Evidence and independent checks.** Run the read-only verifier from the repository root:

```bash
python -B frontier/experiments/i58_standard_map_additive_entropy_novelty/verify.py
```

Its [diagnostics](../experiments/i58_standard_map_additive_entropy_novelty/diagnostics.py) are independently written exact rational checks: 18 synthetic first-crossing schedules, 12 admissible seed exponent pairs, 48 mixed-sign Dirichlet examples comparing an independently differentiated continuant/cofactor quotient with the cubic Green contraction, a singular-matrix negative control, and 10,920 shortfall-count cases. The total is **12,220 exact finite assertions**, with no floating trajectories. The scalar schedules deliberately satisfy doubling and a good seed while allowing unbounded amplification; they are negative controls showing that SC is indispensable, not standard-map counterexamples. The feedback examples likewise show why the mass estimate alone does not close H.

The completed [I57 verifier replay](../experiments/i58_standard_map_additive_entropy_novelty/i57-replay.json) also passes, including 79,968 independent exact assertions and its preserved I52 historical-domain failure. The unchanged [I54 verifier replay](../experiments/i58_standard_map_additive_entropy_novelty/i54-replay.json) passes its 68-artifact seal, 7,327 exact checks, 11 pins, 6 PDF re-extractions, 9,340 corpus blobs and all 170 unchanged I52 sealed artifacts. Its nine floating rows remain explicitly synthetic. This audit’s own verifier checks frozen inputs, exact brief, all direct pin Git blobs, current response bodies, nine PDF re-extractions, passage bindings, and three corpus search **line multisets** (34, 1,833 and 255 lines), against the complete 13,223-entry/749-manuscript tree and 9,340-file ignored corpus. Four shared ledgers are mutable and any live drift is informational; original seals are immutable. No prior archive was recursively copied.

The completed I57 dependency also preserves a distinct historical failure: the direct unchanged I52 verifier stops at `AssertionError: search multiset prior-screens`. Its growing `frontier/iterations` search domain now has exactly 12 later I54 matches added to the original 13, with no removals. The archived failure and both multisets are frozen here and checked without rewriting the old snapshot. The separately replayed I52 diagnostics match all 97,104 assertions; original seals remain intact. This is not reported as a successful vanilla I52 verifier run.

The first preparation attempt misread tree keys by stripping `preprints/`, causing a retained KeyError. A second bookkeeping error counted the common `preprints` prefix as one manuscript; it was corrected to the manuscript component and checked against 749. Both are recorded in [process-notes.txt](../sources/i58_standard_map_additive_entropy_novelty/process-notes.txt). Neither concerns a mathematical failure, a repaired proof, or a refreshed old seal. Evidence replay certifies provenance and finite calculations, not analytic correctness or novelty.

**7. Decision for the parent.** Preserve H as an original-proof-approved technical strengthening under the stipulated premises. Its newly exposed rate is real if SC applies, but paragraph 2 gives a complete noncircular reduction to the already available source mechanism and elementary F; even a constant-threshold, logarithmic-square seed suffices. Preserve G as a useful restricted technical estimate, without crediting it for the open complement or counting its consequences twice. No indispensable new mechanism beyond those premises was identified. There is no missing additional lemma in this contribution reduction conditional on SC and the accepted graph contracts. I57 has now settled the original I54 extraction and graph/coarea applicability questions with PASS ORIGINAL WITHOUT REPAIRS; this review attributes that full original-proof verdict to I57, rather than presenting finite evidence checks as proof certification. Full invariant anti-concentration, constructive renewal tails, effective numerical entropy constants and the exact lower conjecture remain outside what has been proved here.
