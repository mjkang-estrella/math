# Final novelty/significance review r3: full parity and prime-predecessor PD

Date: 2026-10-08. Accepted premise throughout: all applicable theorems of `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. This review does not audit their truth.

**Recommendation: ACCEPT AS ONE SUBSTANTIAL, QUALIFIED DEDUCTION beyond R006.** The additional signed analytic bridge is substantive; the inspected strongest corpus interfaces and established literature do not directly supply the full theorem. The independent r2 mathematical PASS is an input to this review, not its novelty argument. Worldwide priority is not certified. Describe the result as a substantial theorem **under the stipulated corpus**, not as an independently established unconditional breakthrough or a first-ever claim of shifted-prime cancellation.

Two fresh findings materially improve the prior-art record:

- Carella's latest listed arXiv version is **v3, 25 July 2022**, and its actual Theorems 1.1–1.2 explicitly assume Hypothesis 2.1, a distribution hypothesis for the signs **on shifted primes**. The v1-only criticism must not stand in for this current comparison.
- LP implies the exact finite-valuation parity conjecture of **Moree–Hommersom, Conjecture 1, p.21, arXiv:math/0307352v1**, recorded as [MathDB problem 377990](https://mathdb.com/p/377990/parity-conjecture-for-the-mobius-function-on-shifted-primes). The short deduction is given below. This is actual named-problem relevance, without an invented importance score.

I read AGENTS.md, the pin, the complete preprint-path inventory and relevant catalogue entries, the candidate, r2 review, R006 statement, and the newly present [R008 integration](../findings/R008-parity-PD-independence.md). I inspected new pinned source contracts and primary external papers. This is a strongest-premise/novelty review, not a repeated full analytic proof audit. No agents, commits, staging, index edits, external messages, or changes to parent files were made. All evidence writes are in `frontier/{sources,experiments}/i05_parity_novelty_r3/` and this review.

## 1. The result being assessed, without scope inflation

For every fixed positive modulus M and reduced residue b, sample primes p≥3 in either a terminal dyad `(x,2x]` or cumulatively through X. Let V(p−1) be the ranked logarithms of the prime factors, with multiplicity, normalized by log(p−1). For every fixed k and continuous complex H on `[0,1]^k`, LP asserts

\[
 \mathbb E_{p\equiv b\ (M)}[\lambda(p-1)H(V_1(p-1),\ldots,V_k(p-1))]\longrightarrow0.
\]

Together with R006 and the squarefree tail argument this gives

\[
 (V,\lambda,\mu^2)\Rightarrow(\mathrm{PD}(1),S,B),
\]

in every finite ranked-coordinate projection, with mutual independence, S a fair sign, and B Bernoulli with parameter `C_{M,b}` as stated in R008. The local factors include 2 and every prime dividing M. A forced square gives `C_{M,b}=0`; the Liouville conclusion remains meaningful. For M=1, `C=∏q(1−1/[q(q−1)])≈0.3739558`, each Möbius sign has density C/2, and Möbius-weighted continuous ranked tests have zero limit.

This is one finding with several consequences. Squarefree conditioning alone, the classical product C, and the four-atom probability inversion are not separate substantial discoveries. The product's agreement with the familiar Artin constant does not prove a primitive-root density formula.

There is no rate, effective cutoff, growing-modulus statement, general other-shift result, or arbitrary multiplicative-weight extension. In particular LP must not be renamed a proof of the entire Hardy–Littlewood–Chowla conjecture. With H=1, partial summation and the negligible prime-power contribution do give its single predecessor hybrid case, `Σ_{n≤X}Λ(n+1)λ(n)=o(X)`, and the analogous Möbius assertion; this observation explains the classical target, not an enlarged family of shifts.

## 2. Complete-inventory screen and strongest corpus contracts

The screen uses **sources/preprints-tree.json**, whose `truncated` flag is false and which contains 13,223 entries. This file has 749 top-level preprint directories; that is an inventory count, not a claim to have audited 749 proofs or a replacement for the catalogue's notion of distinct manuscripts. I saved all their names, broad title matches, and matching lines of the complete 9,142-line CONTENTS file in [catalogue-screen.json](../sources/i05_parity_novelty_r3/catalogue-screen.json). The broad screen includes primes, shifts, multiplicative functions, Chowla/Elliott, parity, Möbius/Liouville, sieve/squarefree, Dickman, Dirichlet, and arithmetic progressions. Unrelated topology, quantum-parity, and Liouville-geometry matches were excluded by subject. Primitive-root companions were additionally selected explicitly.

Thirty-six relevant TeX files were freshly retrieved from immutable raw URLs. All 36 Git-blob hashes match the complete tree. The full [retrieval manifest](../sources/i05_parity_novelty_r3/retrieval-manifest.json) supplies their paths, URLs, SHA-256 and Git-blob hashes; [source locators](../sources/i05_parity_novelty_r3/source-locators.json) supplies precise lines and independently hashed ranges. TeX references use labels and line numbers rather than invented PDF page numbers.

**O: Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/build/.** I inspected all introductory conclusions, quantitative `01-setup`, `03-analytic`, `07-spectral`, `08-affine`, and the qualitative analytic-transfer and affine/progression contracts. The entire O TeX collection, except its main wrapper, is retained for checking context.

- `introduction.tex`, `thm:q-affine`, and `quantitative/01-setup.tex`, `q:progression`: `O(X/(log X)^c)` for **two Liouville factors** at fixed nonproportional affine forms, including fixed nonunit residue classes. c is some absolute positive exponent; it is not arbitrary logarithmic accuracy. Affine-coefficient constants are not uniform for coefficients growing with X.
- `thm:elliott`, `cor:affine`, and `qualitative/affine-corollaries.tex`, `prop:affine-progression`: **fixed 1-bounded multiplicative functions**, at least one uniformly nonpretentious, with qualitative ordinary-integer `o(X)` cancellation. The paper explicitly disclaims a quantitative rate for this general class.
- `quantitative/03-analytic.tex`, `q:rough-shifts`, averages Liouville correlations over a rough shift family; `q:center` connects its specifically defined sums to the original **integer Liouville-pair** average. `q:testing` bounds that centered object, not a prime-weighted raw average. The qualitative `prop:analytic-centering` fixes the auxiliary B before the long-variable limit and retains the multiplicative-function hypotheses. Its classical `thm:mrt` input is an averaged short exponential-sum bound, not fixed-shift prime cancellation.

These are materially stronger checks than merely observing that the qualitative main theorem says o(X). Substitution of a prime indicator fails multiplicativity; substitution of Λ fails both multiplicativity and boundedness. Even a fixed roughness indicator, which is multiplicative, gives an ordinary-integer limit at that fixed sieve cutoff, not a prime-normalized limit at a growing cutoff. The quantitative two-Liouville theorem has neither a prime-supported arbitrary second factor nor the required growing-divisor uniformity. Inserting a prime weight into a graph test does not automatically preserve the source centering/dilation identity. Thus no direct strongest-scope reduction was found in O, including its quantitative lower interfaces. This is not a claim that no future shorter proof from O could exist.

**D/E/S: the prime-predecessor family.** D is `The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/`; E is `Prime-Predecessors-with-an-Even-Number-of-Prime-Factors-September-17-2026/build/`; S is `Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026/build/`.

- D `sections/01-introduction.tex`, `thm:main`, is unsigned PD. D `sections/06-correlations.tex`, `thm:two-sided` (line 55), has the specific **centered** invariant tuple core `𝒲(Σ1_{ℓ|n}−C_x)`. It is not a general correlation theorem for every bounded first factor.
- E `main.tex`, `thm:main`, gives infinitely many squarefree even-parity predecessors. E `sections/03-shifted.tex`, `sh:sign` (line 64), permits only 1 or the active-band sign; `sh:core` (line 70) has a prescribed invariant prime-slot convolution. `sh:discrepancy` (line 87) concerns α. The proof after `sh:small-square-error` (line 514) explicitly removes the signs of the unmarked m and long prime because they contain no group prime. Full λ does not have that property.
- S `sections/02-transference.tex`, `cor:transference-pairing` (line 1266), really does allow first-vector dependence on position and only forbids dependence on its marks at fixed position. This enables the new lift. It controls an operator residual; it does not by itself eliminate the comparison terms.
- D's actual `cor:sparse-bound` (line 807) is coefficient-independent. Conversely `cor:constant-high` (line 910) comes from an **unweighted** log-phase estimate; it is not a signed Liouville estimate. D §9 `lp:prime-polynomial` (line 16) and `lp:log-phase` (line 251) retain their precise scale/frequency/modulus restrictions. The candidate uses them inside a new comparison argument rather than replacing their input sequences.

**Other plausible stronger premises.** The actual P introduction (`Primitive-roots-for-every-admissible-integer-base-October-4-2026`) states `thm:hecke-zero-free`, a fixed zero-free strip for finite-order Hecke characters over the specified cyclotomic fields, as well as its primitive-root lower bound. Its §8 `lem:marked-coefficient-transfer` supplies the scalar square interface used by CT. Neither conclusion is a theorem about prime-shifted λ; ordinary one-variable zero-free information does not directly evaluate this shifted correlation. T's simultaneous primitive-root theorem and prime-reservoir interface likewise concern primitive-root sieving under their named inputs, not parity/PD independence.

I also read the actual introductory contracts for the joint Dickman law for consecutive **integers**, squarefree/power-free polynomial values (including the simultaneous separable-product corollary), additive indecomposability of the primes, and polynomial differences at prime arguments. They respectively concern unsigned integer largest factors, integer polynomial power-freeness, additive decomposition, and difference-set density. None supplies prime-normalized signed ranked-factor statistics. These were genuine nearby-contract exclusions, not audits of their accepted proofs.

## 3. Why the additional work is nonroutine

The novelty-bearing step is the **signed interior prime statistic**, obtained by coordinating CT, LC, SPR and extraction. It is not each algebraic sign identity considered separately.

CT alone is a useful but short extension: after selecting K inert primes, `λ(ah)=(-1)^Kλ(h)` leaves a bounded residual outside the original scalar Cauchy square. The scalar α/β discrepancy and determinant problem remain unchanged. Its importance is that it allows the later signed composite removal without asserting the false implication that α's cancellation survives α↦λα.

The main analytic adaptation is LC. A sign on the first physical position is permissible under S, but after stripping the shared labels it produces **pattern-dependent signs** `(-1)^{Js-c_ν}`. The physical dyads and full Mellin integral must be reassembled before progression mixing. The original ideal kernels estimate only the residual combination. Bounding its individual signed comparisons requires another argument: use **uncentered, nonempty long tuples**, ordinary-integer BVλ at low time, and the retained long prime with the unchanged sparse Gram kernel at high time. This choice avoids a missing signed constant-term estimate. None of E's printed band-sign theorem, D's centered theorem, or the classical BV theorem alone makes this conclusion automatic.

SPR is a classical distribution theorem applied after a new compatible expansion: a represented-union divisor model, positive Bonferroni error envelope, exact nonunit CRT reduction, and a fixed strict modulus margin (`c₀<ε/8`, BV exponent 1/3). The positive parity split lets the original sieve act on two nonnegative sequences. The sign remains attached to the actual predecessor during allocation; unsigned deweighting bounds the error. Keeping `x→∞`, then the number of arrays, then depth is essential to avoiding a hidden stronger premise.

Finally, signed factorial measures must be transported through the **unsigned size-biased tightness** from R006. Recovering total signed mass from d=1, instead of asserting a d=0 analytic theorem, closes a real interface problem. The sorting and domination tools are standard probability; their use here completes the analytic result. The subsequent finite square exclusion and four-moment inversion are routine consequences and should be credited as such.

The amount of manuscript copied or the number of finite tests is not the significance measure. The reason for a substantial verdict is that the proof supplies the missing sign-sensitive comparison estimates and extraction at **prime normalization**, yielding full parity jointly with macroscopic factor sizes. R006 supplied none of those signed estimates.

Two proposed shortcuts fail at a structural level. PD weak convergence cannot test microscopic parity, which is not a fixed continuous function of finitely many ranked coordinates. Similarly, an Erdős–Kac Gaussian limit for a normalized factor count does not imply its parity: parity asks for a characteristic function at frequency growing with the Gaussian normalization. Even integer-valued variables supported only on even integers can have a Gaussian scaling limit. Neither marginal law implies LP or independence.

## 4. Fresh primary-literature comparison, including current versions

**Ordinary-integer BVλ.** [Pintz, arXiv:1004.1067v1](https://arxiv.org/pdf/1004.1067v1), p.2, (1.5), supplies distribution below exponent 1/2 for λ on integers. Its surrounding discussion separately lists shifted-prime sign sequences. [Shao, ANT 11 (2017)](https://msp.org/ant/2017/11-4/ant-v11-n4-p06-p.pdf), printed p.961, supports the classical background in an exceptional-modulus/centered-mean formulation. These are inputs to LP, not duplicate conclusions. I preserve r2's distinction between their formulations.

**Averages over shifts.** The arXiv history of [Lichtman, 2009.08969](https://arxiv.org/abs/2009.08969) lists v2 (20 October 2021) as latest; I downloaded that exact version. Its Theorem 1.1, p.1, and Remark 1.7, p.3, cover growing shift averages and allow Liouville. The published paper is QJM 73 (2022), 729–757, [DOI 10.1093/qmath/haab054](https://doi.org/10.1093/qmath/haab054). The lower shift-range requirement does not permit H=1 or exclude a particular fixed shift from the exceptional set.

[Lichtman–Teräväinen, Forum Math. Sigma 10 (2022), e57](https://doi.org/10.1017/fms.2022.54), published Theorem 1.2, p.2, and Corollary 1.4, p.3, improve to logarithmic shift ranges but retain exceptional shifts. The statement after Theorem 1.2 explicitly allows λ. I read and retained the **published primary PDF** from the authors' university repository and the current arXiv v3, 21 June 2022. The fixed predecessor case and its factorization-weighted version do not follow from those averages.

**A stronger conditional hybrid theorem.** [Tao–Teräväinen, DOI 10.1112/jlms.12663](https://doi.org/10.1112/jlms.12663), published-layout author PDF, Theorem 1.6, PDF p.4, estimates mixed Λ/λ products with at most two Λ factors **assuming a Siegel zero**, on an explicit range determined by its conductor and quality. This is genuinely closer in target scope than ordinary two-point Chowla. That extra zero-existence hypothesis and restricted scale range are not supplied by the accepted corpus or LP's premises. It is not an all-cutoff unconditional duplicate; invoking it cannot replace the present bridge under the stipulated assumptions.

**A recent 2026 nearby result.** [Biao Wang, arXiv:2609.14492v1, 13 September 2026](https://arxiv.org/pdf/2609.14492v1), Theorems 1.2–1.3, pp.2–3, gives dynamical versions of prime/Λ-weighted Ω statistics, still **averaging h₁** over a growing H (the displayed range starts at `exp(√log N)`). Its stronger dynamical conclusion does not isolate the one required fixed shift. The latest-history page lists only v1. This is a recent preprint comparison, not an assertion of journal validation.

**Carella: the version distinction is essential.** [The current history](https://arxiv.org/abs/2206.12956) lists v1 (26 June), v2 (4 July), and v3 (25 July 2022), with no later version shown. I downloaded v2 and v3. In [v3](https://arxiv.org/pdf/2206.12956v3), p.4, Theorems 1.1–1.2 assume Hypothesis 2.1; p.6 states a shifted-prime distribution hypothesis, not ordinary BVλ. Its q=1 part already contains scalar cancellation for the allowed shift. The proof on pp.19–20 now invokes that hypothesis. The arXiv abstract's unconditional-sounding description is therefore an unsafe substitute for the actual theorem.

V2 still makes unconditional scalar claims (p.4). Its Lemma 4.2, p.20, prints the same `+Q/2` term for both counts, and (73), p.21, cancels it. The exact formula is `(π±Q)/2`; substitution gives only Q=Q. V3 retains a similar erroneous standalone Lemma 3.2 on p.18, but its revised main theorem is explicitly conditional. This is a fresh inspection, not an extrapolation from v1. Neither version supplies an established unconditional duplicate of LP; neither supplies its joint PD conclusion. No separate later correction or journal proof was located by the bounded searches.

**What is and is not cleared.** The complete new joint law is not stated in any inspected external source. Earlier overlapping *claims* do exist. Failure to find a further proof is not worldwide-priority evidence strong enough to certify priority. Even a valid earlier scalar cancellation theorem would not, without an additional argument, imply independence from V. The current verdict is a qualified research judgment based on actual contracts, not an exhaustive literature theorem.

## 5. Named-problem significance and exact MathDB match

[MathDB 377990](https://mathdb.com/p/377990/parity-conjecture-for-the-mobius-function-on-shifted-primes) records the parity conjecture for the Möbius function on shifted primes, attributed to Moree–Hommersom. On inspection it is marked open, with no posted solutions and no refreshed progress summary. I did **not** observe a defined importance score or ranking. Its displayed counters must not be reinterpreted as such a score. This is evidence of a concrete recorded problem, not independent verification of present mathematical status.

The primary source is [Moree–Hommersom, arXiv:math/0307352v1](https://arxiv.org/pdf/math/0307352v1), 27 July 2003. Definitions and Proposition 6 are on p.20; **Conjecture 1 is on p.21**. The paragraph introducing it calls the underlying cancellation conjecture “thought to be deep by the experts.” It concerns primes p−1, not just an analogy with positive shifts. The current arXiv history lists v1 only. The manuscript is not being represented here as a published journal article.

Here is an explicit deduction from LP of that exact conjecture; this is a significance check, not another counted substantial finding. Fix a finite set `S={q₁,…,q_t}` and nonnegative fixed valuations `e₁,…,e_t`. Let

\[
 A(p)=\mathbf1_{v_{q_j}(p-1)=e_j\ \forall j},\qquad
 B_S(n)=\mathbf1_{q^2\nmid n\ \forall q\notin S}.
\]

The source defines μ_S to ignore the primes in S and vanish unless n is squarefree outside S. On A(p)=1, complete multiplicativity gives the exact identity

\[
 \mu_S(p-1)=(-1)^{e_1+\cdots+e_t}\lambda(p-1)B_S(p-1).
\]

For fixed Y replace B_S by the finite product excluding squares of `q≤Y, q∉S`. Both this product and A are residue conditions modulo the fixed integer

\[
 Q_Y=\operatorname{lcm}\left(\prod_{j=1}^t q_j^{e_j+1},
                   \prod_{q\le Y,\ q\notin S}q^2\right).
\]

After discarding finitely many primes dividing Q_Y, the selected primes form a finite union of reduced classes. Apply LP with H=1 to each, and sum using their fixed-progression prime proportions. The normalized signed sum tends to zero for each fixed Y. The unsigned square tail from the LP squarefree argument bounds the replacement error by O(1/Y) in limsup. Let Y→∞. Thus

\[
 \sum_{\substack{p\le X\\v_{q_j}(p-1)=e_j\ (1\le j\le t)}}
            \mu_S(p-1)=o(\pi(X)),
\]

which is the source's Conjecture 1. Incompatible valuation conditions contribute at most finitely many primes. This reasoning also covers e_j≥2: one must exclude squares only **outside S**, rather than apply the full μ² corollary in a forced-square class. No growing-modulus estimate is used, since Y is fixed before X tends to infinity.

The same deduction could retain a fixed continuous H, but the displayed H=1 implication already establishes the precise named-problem relevance. It strengthens the significance case beyond numerical parity balance. Separately, the published Lichtman–Teräväinen introduction, p.3, identifies shifted-prime Möbius cancellation as a model case for the parity problem in sieve theory. These are defensible qualitative significance statements. They do not establish a numerical “high importance” rank.

## 6. Proof-critical caveats and integration recommendation

No new proof-critical defect emerged from this focused review. I do not claim to have rerun r2's full proof audit. I checked the source boundaries most likely to undermine the novelty argument: E's sign domain, O's quantitative versus qualitative scopes, S's endpoint restriction, D's sparse versus constant-term interfaces, and the new named-problem deduction.

Retain the r2/R008 safeguards: original α discrepancy and ideal kernels; one physical sign with the correct shared-label count; complete dyad/Mellin reassembly; nonempty long tuple; ordinary-integer BV with the nonunit reduction and strict exponent gap; positive parity sieve weights; the original predecessor sign outside allocation; unsigned deweighting; weak signed convergence with unsigned boundary domination; and the stated order of limits. Dropping any of these is not justified by this novelty verdict.

The candidate does more than establish a correct corollary of a stronger printed theorem. It extends the corpus's signed analytic reach and achieves a historically identified fixed-predecessor parity target with joint factorization information. **Recommend closing the second substantive-discovery gate with this one qualified finding**, after updating the prior-art paragraph to cite Carella v3's conditional theorem and the exact Moree–Hommersom implication. The parent owns any integration and commit. No independent proof of the corpus, human peer review, formal verification, external publication, or worldwide priority certification is claimed.

## 7. Reproducible evidence and retrieval limits

Evidence is local to the assigned directory:

- [retrieval-manifest.json](../sources/i05_parity_novelty_r3/retrieval-manifest.json): 36 fresh pinned TeX files plus eight initial external downloads, all successful; each pinned file matches the complete tree's Git blob.
- [literature-additional-manifest.json](../sources/i05_parity_novelty_r3/literature-additional-manifest.json): eight more successful primary/database downloads, including the published LT PDF, its arXiv v3, Moree–Hommersom, the published-layout Tao–Teräväinen PDF, and Shao.
- [source-locators.json](../sources/i05_parity_novelty_r3/source-locators.json) and [page-locators.json](../sources/i05_parity_novelty_r3/page-locators.json): 34 hashed source-label ranges and 25 precise PDF-page extracts. PDF pages 4 and 6 of Carella v3 and p.21 of Moree–Hommersom were visually checked; Carella pp.18–19 were also checked. Rendered PNGs are retained.
- [input-snapshot.json](../sources/i05_parity_novelty_r3/input-snapshot.json): hashes of the nine local records used, including R008 after it appeared. These parent records may change concurrently; this review never modifies them.
- [research-log.json](../sources/i05_parity_novelty_r3/research-log.json): bounded search queries, primary records, current-version checks and the failed web retrieval. The Cambridge article-page open timed out; this did not prevent inspection and retention of the published PDF through the university repository. No inaccessible source is counted as read.

Selected exact SHA-256 hashes, with complete hashes for every retained source in the manifests:

```text
Carella v3 PDF       388d1903735f9bc28055e5d6d554055f002734a0271adadb91a7a848c3161e35
Carella v2 PDF       4299eb3eb7e7211051428701dd5588661611045b1815130fbd405b3b4fa98816
Moree–Hommersom v1   ff9498ea4b87e6085c6a4507d8b7a2a86b63aa3bb54387f77c677fe8aa78ea5a
LT published PDF    68eaf812e570fa11fa6db69cb50107defdef05f7cbed43901d52d25973ee4a05
Lichtman v2 PDF     7f7421c328f01dcf18565b1840a0d9e66e9f901ee966b414c8bde5f9e49a4456
Wang v1 PDF         2cb2a1357daf9fbfe21d81661da9039ae60520440887416c64bb2942a2ff19ea
```

The retrieval scripts and evidence recorder are in the assigned experiments directory. [Final validation](../sources/i05_parity_novelty_r3/validation.json) found no source-hash, pinned-blob, source-range, or local-link errors. The shared iteration index changed concurrently and was reread; no theorem input changed. File hashes establish identity, not correctness or novelty. No finite numerical parity experiment was needed for this review, and none is offered as evidence for an asymptotic theorem.
