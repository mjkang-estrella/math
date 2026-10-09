# Final prior-art and significance audit: complex prime-predecessor modes

Review date: 2026-10-08, America/Los_Angeles; retrieval records use UTC, 2026-10-09. Premise: all applicable theorems at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are true by user stipulation.

**Recommendation: ACCEPT as ONE additional substantial, qualified deduction.** The novelty-bearing object is the nonreal-mode marked prime-extraction bridge, including its common physical principal model and aggregate principal-term cancellation. This is more than a routine replacement of the parity parameter in R008. Finite Fourier inversion, residue equidistribution, conditional PD laws, and the dyadic/cumulative formulations belong to this one bridge, not separate findings.

This recommendation does not accept a new numbered finding or change any count. Exactly **R006, R008, and R009** are presently accepted; the user’s target remains **ten substantial nonroutine findings**. Earlier historical counts appearing in input documents are not current instructions. No R number is assigned here.

The independent [round-2 proof audit](i10-complex-prime-modes-r2.md) remains **PASS**. No decisive new proof defect emerged from the source-contract and reduction checks in this review. This is an independent significance/prior-art assessment, not a second complete proof audit and not an audit of upstream truth. Worldwide priority is not certified by a finite search.

## 1. Exact object assessed

I read the complete [856-line candidate](../iterations/i10-complex-prime-modes.md), complete 326-line proof audit, [proof-integration note](../iterations/i10-complex-modes-proof-integration.md), complete [i07 arithmetic report](../iterations/i07-arithmetic.md), accepted [R006](../findings/R006-progression-PD-primitive-root-density.md) and [R008](../findings/R008-parity-PD-independence.md), and their relevant proof and novelty reviews. The candidate’s SHA-256 is:

```text
cd87b7cf1636395410aeb90dc431eae695d43f7e824b7fd0a49ddd04ca4a3409
```

For fixed (M\ge1), ((b,M)=1), fixed (m\ge3), (a\in\mathbb Z/m\mathbb Z), fixed (k), and continuous complex (H:[0,1]^k\to\mathbb C), CP asserts

\[
 \frac{1}{\pi(X;M,b)}
 \sum_{\substack{3\le p\le X\\p\equiv b\pmod M}}
 1_{\Omega(p-1)\equiv a\pmod m}
 H(V_1(p),\ldots,V_k(p))
 \longrightarrow \frac1m\mathbb E H(\mathrm{PD}(1)_{1:k}).
\]

The analogous prime-class-normalized terminal dyadic limit also holds. Factors are ranked with multiplicity and normalized by (log(p-1)). Every parameter is fixed before the limit. There is no rate, growing-(m) statement, uniformity over roots approaching 1, or new primitive-root-density assertion. The modes (z=1) and (z=-1) are inherited from R006 and R008.

The analytic addition is candidate (2): for each fixed nonreal root of unity (z), every nonempty interior long-prime tuple statistic (T_x) of the specified form, and the fixed progression,

\[
 \sum_{\substack{p\equiv b\pmod M}}
 \Phi((p-1)/x)z^{\Omega(p-1)}T_x(p-1)=o(x/\log x).
\]

Here tuple primes are at least (x^\epsilon), and their product is at most (x^{1-\epsilon}). This is a **factorization-weighted, fixed-shift prime-scale estimate**. A theorem about ordinary integers, unmarked prime averages, normalized Gaussian factor counts, or averages over the shift is not the same contract.

## 2. Comparison with the strongest inspected pinned interfaces

The search used the complete `sources/preprints-tree.json`: **13,223 entries, 10,373 blobs, 749 manuscript directories, `truncated:false`**. It did not use the ignored truncated tree as its inventory. Thirty-six selected pinned files were freshly retrieved and their Git blob identities checked against that tree. The entire tree was screened, not semantically read in full. Exact file URLs, hashes, and inspected ranges are retained in the evidence directory.

Abbreviations: D = *The Poisson–Dirichlet Law for Prime Predecessors*; S = *Weighted Dilation Graphs, Smooth Shifted Primes, and Totient Fibers*; E = *Prime Predecessors with an Even Number of Prime Factors*; P = *Primitive Roots for Every Admissible Integer Base*; O = *Ordinary Two-Point Correlations of Multiplicative Functions*; Z = the two *Quasi-Riemann Hypothesis* versions. The paths below refer to their pinned `build/` trees, whose full names and immutable URLs are in the [retrieval manifest](../sources/i10_complex_modes_novelty_r3/retrieval-manifest.json).

| Prior result and exact interface | Prior hypotheses and conclusion | Inherited here | Missing implication / actual addition |
|---|---|---|---|
| R006, AP; D `sections/01-introduction.tex`, `thm:main` | D gives unsigned finite-dimensional PD over all primes. R006 supplies that law in every fixed reduced progression, including (b-1) nonunit modulo (M). | Progression lifting, unsigned tightness, size-biased truncation and sorting. | Neither marginal PD nor its progression refinement determines microscopic (Omega\bmod m), or independence from that residue. |
| R008, LP; its LC, SPR and CT arguments | Full (\lambda(p-1)=(-1)^{\Omega(p-1)}) cancellation with the interior tuples, then parity/PD independence in fixed progressions. | Physical-position insertion, shared-label accounting, nonempty tuples, positive sieve splitting, order of limits and dominated signed probability argument. | R008’s zero-principal-mean argument does not apply to nonreal (z). The candidate must retain, match, propagate and finally recombine a nonzero principal model. |
| E `main.tex`, `thm:main`; `sections/03-shifted.tex`, `sh:sign`, `sh:core`, `sh:discrepancy` | Infinitely many squarefree even predecessors. The lower correlation theorem permits **1 or an active-band parity sign**, common to both endpoints; it has a prescribed invariant prime-slot convolution and discrepancy hypothesis on its rough coefficient (\alpha). | Signed graph precedent and extraction architecture. | This is not an arbitrary complex completely multiplicative first weight. The proof at lines 505–552 uses that the unmarked rough variable and long prime contain no active-group prime. Full (z^{\Omega}) instead inserts (f_z(m)); the required principal discrepancy is then false without centering. |
| S `sections/02-transference.tex`, `cor:transference-pairing`; D `sections/06-correlations.tex`, `prop:graph-transfer`, `prop:ideal-family` | The first endpoint may depend on physical position but must be independent of marks at that position, with the required supremum/norm bounds. The theorem bounds a raw-minus-comparisons **residual**. | This broad endpoint freedom, physical ideal operator, kernels, determinant estimates and coefficient-independent transfer. These are not new. | A residual bound does not bound each comparison or the raw term separately. One common covariant (\mathcal B_x) makes the nonreal centered endpoint admissible; PM separately controls its comparison terms. |
| D `sections/06-correlations.tex`, `thm:two-sided` | The printed first statistic is specifically (\mathcal W(T_x-C_x)); the other factor is invariant under removal of group primes. | Centered tuple method and major/minor-arc framework. | Multiplying the printed centered statistic by (f_z) does not magically cancel its new Mellin principal density. D’s constant (C_x) cannot substitute for the new smooth-part-dependent model. |
| D `cor:sparse-bound`, `cor:constant-high`; `sections/09-long-prime-appendix.tex`, `lp:prime-polynomial`, `lp:log-phase` | Sparse Gram bounds are coefficient-independent. The constant comparison’s high-time input is an **unweighted** discrete log-phase estimate, in explicit length/time/modulus ranges, permitting nonunit residues. | The retained long prime and high-time comparison method. | The candidate must decompose its model into discrete progressions and retain the actual (Y,H',P_s,a,e) scales. This is a technical adaptation, not an independently novel exponential-sum theorem. It is nevertheless required for the common-model bridge. |
| D `sections/07-extraction.tex`, especially lines 380–419 and 490–620 | Positive tuple mass, coin expansion, represented-union removal, (j^{|P|}) allocation factors and arbitrary-log bounds for each **already centered** error. | Coins, allocation identities, unsigned exceptional-set control and sieve machinery. | Absolute summation of the candidate’s surviving model terms would lose powers of (log x). Reversing **all signed allocations and coins before absolute values**, while keeping the same physical model, supplies a new aggregate bound. |
| P `sections/08-type-ii.tex`, `lem:marked-coefficient-transfer`; S shifted/type-II interfaces | Rough positive-power dyadic coefficients satisfy the stated all-character, low-time arbitrary-log discrepancy. Selected-prime scalars sit outside the common scalar Cauchy argument. | The type-II step with (z^K) outside that square; the original coefficient problem is unchanged. | This step alone is a routine extension of R008. It neither proves principal matching nor removes the aggregate complex model. |
| O `introduction.tex`, `thm:elliott`, quantitative affine theorem; qualitative `analytic-transfer.tex`, centering proposition | Qualitative ordinary averages for fixed 1-bounded multiplicative functions, one uniformly nonpretentious. Quantitative logarithmic saving is stated for the specified Liouville affine correlations. The lower centering estimate has fixed auxiliary parameters before (X\to\infty). | Ordinary multiplicative cancellation background and general graph ideas. | (mathbf1_{n+1\text{ prime}}) is not a multiplicative second function; (\Lambda) is neither 1-bounded nor multiplicative. An (o(X)) error can hide all (X/\log X) primes. No inspected lower interface supplies the growing presieve, tuple marking and arbitrary-log principal matching of CP. |
| Z September 30 `paper.tex`, main theorem; October 5 `paper2.tex`, zero-free theorem and prime-AP corollary; P `thm:hecke-zero-free` | Z gives respectively the stated (7/8) and (11/12) zero-free half-planes for its named L-functions; the latter prime-AP error has exponent (11/12). P gives width (10^{-6}) over the specified cyclotomic fields, with principal poles allowed. | Strong zero-free information for the classical scalar inputs. All is accepted here. | These are not GRH, level-one Elliott–Halberstam, or fixed shifted-prime (f_z) correlations. In particular, zero-freeness does not eliminate the principal branch at (s=1). The October version is not a stronger numerical strip. |
| Joint Dickman `sections/distribution.tex`; totient `source/companion.tex`; deterministic polynomial factorization `sections/10-analytic.tex` | Joint binwise factor data at consecutive **integers**; weighted tuple statements for least totient preimages; a Hecke prime-ideal asymptotic, respectively. | Useful nearby stronger-contract checks. | Integer bins omit the microscopic factor count and cannot be conditioned on a density-zero prime event without additional estimates. The other two interfaces contain neither the required (f_z) weight nor the prime-predecessor joint law. |

This is an actual source-contract comparison, not exclusion by titles. In particular, I have credited the full generality of S’s position-dependent endpoint and D’s coefficient-independent sparse estimate. Those stronger lower interfaces make the construction possible, but do not already state its conclusion.

## 3. Why the difference from R008 is substantive

### 3.1 A concrete obstruction to the substitution ( -1\mapsto z )

Write (f_z(n)=z^{\Omega(n)}). Its Dirichlet series is

\[
 F_z(s)=\zeta(s)^zG_z(s),\qquad
 G_z(s)=\prod_p(1-p^{-s})^z(1-zp^{-s})^{-1}.
\]

For fixed nonreal unit (z), (G_z(1)\ne0) and (1/\Gamma(z)\ne0). Selberg–Delange therefore gives a leading ordinary mean

\[
 \sum_{n\le R} f_z(n)
 =\frac{G_z(1)}{\Gamma(z)}R(\log R)^{z-1}
  +O_z(R(\log R)^{\Re z-2}).
\]

Thus even the modulus-one zero-principal arbitrary-log estimate used for parity fails for general nonreal (z). At (z=-1), all the reciprocal gamma factors (1/\Gamma(-1-j)) vanish; that cancellation is exceptional. For some nonreal roots the ordinary main term is already smaller than (R/\log R), but it still does not have the arbitrary-log saving needed after all intermediate costs. For roots near 1 even its first scale is much larger. This distinction is mathematical, not merely a more cumbersome notation.

The explicit density polynomial is classical input, not a new discovery. What must be added is a representation of **that whole principal contribution** compatible simultaneously with the physical graph, all-small-prime removal, local Fourier testing, nonunit progressions, the presieve and the final allocations.

### 3.2 The candidate supplies that representation

With (L=\log x), (y=\exp(L^{.46})), and (n_y) the full (y)-smooth part, the candidate constructs a single (\mathcal B_x) using the full finite density expansion

\[
 b_{z,y,N}(v)=\sum_{j<N}
 \frac{(A_zP_{z,y})^{(j)}(1)}{j!\Gamma(z-j)}
 (\log v)^{z-1-j},
 \quad P_{z,y}(s)=\prod_{p\le y}(1-zp^{-s}),
\]

with (A_z(s)=((s-1)\zeta(s))^zG_z(s)), a fixed smooth cutoff, the tuple reciprocal weights, and the factor (f_z(n_y)/V_y), where (V_y=\prod_{p\le y}(1-1/p)). In the candidate’s notation,

\[
 \mathcal B_x(n)=\frac{f_z(n_y)}{V_y}\,z^d
 \sum_{\boldsymbol\ell}\frac1\ell
 \beta_{z,y,N}\!\left(\frac{n}{n_y\ell}\right).
\]

The exact formula has **no active-set or allocation index**. It satisfies, including overlapping prime divisors,

\[
 \mathcal B_x(an)=f_z(a)\mathcal B_x(n)quad(P^+(a)\le y),
 \qquad
 \sup_{n\asymp x}|\mathcal B_x(n)|
 \ll L^{-.54(1-\Re z)}.
\]

The estimate keeps the cancellation in the Euler derivatives before bounding them. Discarding lower density terms would not leave an arbitrary-log local remainder; replacing this by an active-band-dependent model would break the final common-factor recombination.

The local matching, PM and PR are interlocking uses of this construction, not three countable findings:

* At low times the rough Selberg–Delange expansion is derived from the **fixed** (f_z), with short Bonferroni divisors and positive error envelopes. It matches the full principal polynomial with the additive residue tests and allowed smooth-part multipliers. It does not apply a fixed-function theorem blindly to a changing rough cutoff.
* At high times the model has a separate discrete progression estimate. Its roughness expansion has coefficients (\mu(e)), not (\mu(e)f_z(e)); it uses whole-interval mean squares before the high-time exceptional-set summation. This is why a low-time density expansion alone was insufficient.
* PM carries (f_zT_x-\mathcal B_x) through the complete residual. The shared-label phase is (z^{Js-c_\nu}), with inverse phase (z^{-c_\nu}), and physical dyads/Mellin integrals are recombined before residue mixing.
* PR sums the presieve discrepancy, rather than proving only an isolated progression estimate. The compatible nonunit CRT reduction is (q=rM/g), (g=(b-1,M)); the local density corrections at primes (>y) have total (O(L^C/y)). The genuine and model principal terms match. Positive envelopes control the truncation errors.

These additions address the exact missing nonreal CM contract recorded in i07. That report already declined to count the scalar Dirichlet-series/Selberg–Delange observation as substantial. Nothing in this verdict reverses that judgment.

### 3.3 The aggregate estimate is the decisive final improvement

For each fixed (z\ne1), the exponent (\delta_z=1-\Re z) is positive, but over the possible fixed orders it can be arbitrarily small. A bound of the shape

\[
 L^C\sup|\mathcal B_x|\,x/L
\]

does **not** prove the stated all-fixed-(m) theorem. The issue cannot be disposed of by saying all parameters are fixed: (C-.54\delta_z) can remain positive for the fixed root in question.

The candidate reverses the complete signed allocation and coin expansion, retaining coefficients ( (-1)^{|T|}c_1^{|P|}j^{|P|}), before applying absolute values. The same physical (\mathcal B_x(u)) then factors out. What remains is the retained probability, between 0 and 1, inside the original positive proxy. Its total mass is (O_{j,K,\gamma,\Phi,M}(x/L)); dependence on the fixed presieve parameter (\gamma) is allowed. Consequently the **combined** model mass is

\[
 O_{N,z,\epsilon,d,j,K,\gamma,\Phi,M}
 \bigl(xL^{-1-.54\delta_z}\bigr)=o(x/L).
\]

Unsigned failure mass is removed before expansion. Bounding individual absolute model terms instead would destroy precisely the cancellation needed here. D and R008 supply the coin/allocation algebra, but their zero-main-term applications did not have to make a nonzero model common to every term and preserve it until this final positive estimate.

This compatibility construction, culminating in a prime-scale aggregate saving for every fixed nonreal mode, is a sufficient substantive advance beyond R008. The individual gamma calculation, type-II phase, finite Fourier transform, and probability sorting argument are routine; I do not attribute separate novelty to them.

### 3.4 Explicit shortcut checks

There is no logical reduction from the *conclusions* of R006 and R008 alone. A random residue modulo 4 with probabilities ( (1/2,1/2,0,0)), independent of a PD partition, has exactly balanced parity and the required unsigned PD marginal, but its (i)-mode is ((1+i)/2\ne0). This is a countermodel to the proposed implication, not a model of actual primes.

Likewise, a uniform truncated residue (A\pmod m) may have an omitted cofactor residue (B=-A\pmod m), making the full residue constant. Small-prime equidistribution and a PD marginal do not imply the target joint law. A normalized Gaussian limit also cannot resolve a fixed lattice residue: a variable supported on even integers can have that Gaussian scaling limit.

The [exact finite checks](../sources/i10_complex_modes_novelty_r3/reduction-checks.json) verify the first two countermodels and the signed-versus-absolute inclusion-exclusion identity. They do not test an asymptotic theorem. They supplement, rather than establish, the source-based nonroutine judgment. I found no explicit reduction from a stronger inspected source which avoids the principal-model problem.

## 4. Current primary-literature audit

The following comparison uses actual theorem statements, primary PDFs and version histories, not search-result titles. Retrieval failures and search queries are retained. The scope distinction in the rightmost column is essential.

| Primary source / version and inspected statement | Actual hypotheses and strongest relevant conclusion inspected | Relation to CP |
|---|---|---|
| [Granville–Shao, arXiv:1706.05710v1](https://arxiv.org/pdf/1706.05710v1), Theorem 1.1(b), §2; [published version](https://discovery.ucl.ac.uk/1568745/1/Granville_New%20B-V-mult-fn-revision_VoR.pdf), Theorems 1.1 and 2.1 | In the class (\mathcal C), defined by (|\Lambda_f|\le\Lambda), prime-restricted BV plus the **centered** Siegel–Walfisz criterion for (f) gives BV for (f). The explicit theorem supplies scale-dependent uniform hypotheses. | Valid ordinary-integer distribution input. For (f_z), prime restriction is (z\mathbf1_{\mathbb P}); inverse is (\mu f_z\in\mathcal C). Part (b) does **not** separately demand inverse SW. It preserves the principal average; it does not estimate (\sum_p f_z(p-1)H(V)). |
| [de la Bretèche–Tenenbaum, arXiv:2010.12929v8](https://arxiv.org/pdf/2010.12929v8), Theorem 1.2 and (1.9)–(1.12) | For (f\in\mathcal F(r,\sigma)) and prime discrepancy (f(p)-\rho) satisfying (1.2), a finite Selberg–Delange expansion with explicit gamma coefficients and the stated remainder. For (f_z), take (r=1), (1/2<\sigma<1); prime discrepancy is zero. | Supplies arbitrarily deep **fixed-function** expansions. The cumulative coefficients contain the Perron (1/s); the candidate’s density is obtained by the corresponding differentiation/partial summation. It supplies neither the physical common model nor its marked shifted-prime extraction. |
| [Granville–Shao, arXiv:1703.06865v2](https://arxiv.org/pdf/1703.06865v2), Corollary 1.1, Theorem 1.2, §1.3; [Drappeau–Granville–Shao, arXiv:1704.04831v2](https://arxiv.org/pdf/1704.04831v2), Theorems 1.2 and 2.1 | General (\mathcal C) distribution with exceptional-character corrections; smooth-supported versions extend the modulus range, the latter to (x^{3/5-\epsilon}) with its specified (y)-range or enlarged exceptional set. | Stronger distribution companions were checked. Smooth-supported is not rough-supported; corrected ordinary congruence sums are not prime-shifted marked sums. A larger level alone does not remove the principal correction or establish CP. |
| [Fouvry–Tenenbaum, arXiv:2004.04766v4](https://arxiv.org/pdf/2004.04766v4), Definition 1.1, Theorems 1.5, 1.8, 2.1 and 2.3 | For divisor-bounded functions essentially periodic on prime intervals/residue classes, centered distribution estimates, including a signed inner sum over moduli near level 1; applications give Erdős–Wintner laws under convergent-series hypotheses and Gaussian laws for shifted additive level sets. | Includes (f_z) in the ordinary multiplicative class. The signed inner modulus sum cannot be promoted to arbitrary sieve weights. The additive convergence hypotheses exclude (\Omega) in the unnormalized Erdős–Wintner application; the Gaussian application does not give fixed-root cancellation or PD marking. |
| [Ford, arXiv:2408.03803v4](https://arxiv.org/pdf/2408.03803v4), Theorems 1, 2, 4 and Corollaries 3, 5 | Under the stated prime-distribution hypothesis (Z(\gamma)), a Kubilius total-variation model for shifted-prime factors (\le y), with error including (e^{-\alpha u\log u}), (u=\log x/\log y), (\alpha<\gamma), and arbitrary inverse-log terms. (Z(1/2)) is available classically. Count-vector Poisson and integer/shifted-prime transfer results concern those truncated primes. | Very relevant microscopic information, but the vanishing-error use requires (u\to\infty). It leaves the large-factor cofactor phase uncontrolled. Taking (y\asymp x) leaves (u\asymp1), even under (Z(1)). It does not provide joint full (Omega\bmod m) and ranked PD. |
| [Bharadwaj–Rodgers, arXiv:2402.11884v4](https://arxiv.org/pdf/2402.11884v4), Proposition 2, Theorem 7, Lemma 8 | Nonnegative sequences with index, congruence bounds and distribution level 1 have PD(1); positive lower levels yield tuple correlations only on restricted support. Shifted primes have level (1/2); their level 1 is a stated conjectural input. | No mode or residue selection. Applying the theorem to the residue-selected prime sequence would require new divisibility estimates for that sequence, essentially the missing marked problem. The stipulated zero-free strips do not supply the asserted level-one hypothesis. |
| [Timofeev, Math. USSR Izvestiya 39 (1992), 1189–1211](https://www.mathnet.ru/eng/im971), Theorems 1–3 and Corollaries 1, 5; full English PDF retained | Theorem 1 gives an upper bound for (f(p+a)=\zeta) with leading factor (4/q), plus ordinary progression sums; it is not a (1/q+o(1)) asymptotic. Theorem 2 and Corollaries give nonconcentration / modulus bounded away from 1 under their hypotheses. Theorem 3 gives a scalar asymptotic assuming a weighted approximation to a primitive character times (n^{it_0}). | Strong classical overlap in subject, but not scalar equidistribution of all (f_z), much less its joint PD version. For fixed nonreal (z), the character-pretentiousness hypothesis fails. The corrected nonpretentious shifted-prime cancellation assertion is stated as a conjecture on printed p.1191, not proved there. |
| [Germán, 2011](https://ac.inf.elte.hu/Vol_035_2011/doi/125_35.pdf), introduction’s Kátai–Hildebrand–Timofeev theorem and Theorem 1 | Requires convergence of the prime pretentious-distance series for a fixed primitive character and real twist; extends scalar mean formulas to shifted integers with a specified number of distinct prime factors. | Confirms the hypothesis boundary in the classical mean-value route. It does not extend the formula to the nonpretentious (f_z) case by simply setting the Euler-product mean to zero. |
| [Gorodetsky–Grimmelt, published QJM 75 (2024), 695–713](https://ora.ox.ac.uk/objects/uuid%3Ab12c6ae9-e2c1-4b2d-8635-9b64bf0516e6/files/rfn107041m), Theorem 1.1, Proposition 1.3, Corollary 1.4 and Remark 2.1 | Samples (m\le n) proportional to (2^{\omega(m)}\mathbf1_{n-m\text{ prime}}). Proves a Gaussian law; proves that **if** its ranked factors converge to PD((\theta)), then (\theta=2), and obtains restricted-support PD(2) correlations. | Different measure and moving reflection. It does not assert full PD convergence in that model, nor a joint modular (\Omega) law for equally weighted fixed prime predecessors. Its explicit lower-order correction is an important precedent, not the candidate’s physical model. |
| [Charamaras–Richter, arXiv:2412.17583v3](https://arxiv.org/pdf/2412.17583v3), Theorems A–C, Remark 1.6 | Logarithmic ordinary-integer independence for bounded functions of (\Omega(n)), (\Omega(n+1)). The appendix improves the error to (O((\log\log N)^{-1/2})). The shifted-almost-prime application averages over typical factor counts. | Even choosing an indicator of factor count 1 leaves an error too large to isolate prime mass. The “typical” count is around (\log\log N), not the fixed count 1. No PD mark or ordinary prime-normalized fixed-shift conclusion. |
| [Wang, arXiv:2609.14492v1](https://arxiv.org/pdf/2609.14492v1), Theorems 1.2–1.3 | Dynamical prime/prime-tuple-weighted factor-count averages, **averaging one shift over (H\ge\exp(\sqrt{\log N}))**, with other shifts fixed and the theorem’s normalization. | A current 2026 close result, but its growing shift average does not isolate shift (-1). Additional dynamical generality does not remove that restriction. |
| [Elliott, Kyoto 886 (1994)](https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/0886-01.pdf), Theorems 1–2 | Structure of the multiplicative group generated by shifted primes; the quotient has order at most 4, with bounded-length representations for powers. | Algebraic generation/nonconcentration is not an equal-density theorem for modular factor counts or a joint ranked-factor law. |

The Ford v4 history observed here is 19 January 2026; Bharadwaj–Rodgers v4 is 9 April 2026; Charamaras–Richter v3 is 17 August 2026; Wang v1 is 13 September 2026. Version dates can differ from the date printed inside the PDF. The current histories inspected for the two distribution companions gave GS v2 and DGS v2; Fouvry–Tenenbaum’s observed latest version was v4. Exact retrieved bytes, including published versions, are identified by their hashes rather than a claim that an unversioned URL can never change.

Hildebrand’s original 1989 publisher PDF returned HTTP 403. I do not count it as fully read. Its accessible primary abstract and Timofeev’s actual reproduction and strengthening were inspected; Timofeev’s successful full PDF resolves the most important theorem-scope question. The first MathNet PDF attempts redirected to HTML or failed; a later `getFT` request succeeded. The retained images of printed pp.1191–1192 verify the formulas which OCR damaged, especially the **(4/q)** in Theorem 1 and the weighted character hypothesis in Theorem 3.

The earlier R008 novelty review also checked conditional mixed (\Lambda/\lambda) results under a Siegel-zero hypothesis and Carella’s version-dependent scalar claims. Those are inherited literature leads, not newly verified full papers in this audit. CP supplies neither a Siegel-zero existence premise nor a shifted-prime distribution hypothesis by stipulation, and a scalar parity result would still not imply its nonreal joint conclusion. I have not converted an inaccessible source or an earlier review’s search failure into evidence of worldwide priority.

## 5. Significance decision, qualifications and proof integration

The positive significance case has two parts. First, CP resolves every finite cyclic factor-count observable jointly with macroscopic factor sizes in fixed progressions. This is strictly more information than parity, a Gaussian marginal, or PD alone. Its scalar specialization is a concrete family within the corrected nonpretentious shifted-prime cancellation problem recorded by Timofeev. This does not solve that entire conjecture, and the parity part is already credited to R008.

Second, the proof adds a mechanism for extracting primes in the presence of a nonzero complex principal density: one covariant model works across the analytic comparisons and the signed combinatorial recombination, with no fixed logarithmic loss at the end. That is the new mathematical work. Standard ingredients, manuscript length, number of source files, numerical agreement and unsuccessful searches are not the reason for acceptance.

The alternative verdict **TECHNICAL ONLY** would be appropriate for just the scalar SD expansion, (z^K) type-II replacement, complexification by real and imaginary parts, or Fourier consequences of an already available all-mode estimate. It is not appropriate for the completed bridge because none of the inspected prior statements supplies that estimate, and the actual parity proof has the explicit nonvanishing-principal obstruction above. Nor did I find a reduction through a stronger rough-density or Dirichlet-character statement that automatically satisfies all of PM, PR and the final aggregate mass bound.

Preserve the four [integration clarifications](../iterations/i10-complex-modes-proof-integration.md) verbatim in substance:

1. Begin positive-envelope sieving with real, nonnegative (\Phi); extend by linearity afterwards.
2. Use (Y=xH'), (H=H'/L^{C_6}), (T_0=xL^{C_6+1}), (H'\ge\exp(2L^{.39}-O(1))), and small-label scale (P_s\le\exp(L^{.36})). Thus the discrete interval (Y/P_s) is much longer than (T_0). The density expansion is not asserted at all high times.
3. For Granville–Shao, the inverse is (\mu f_z\in\mathcal C); use the actual part-(b) hypotheses, without inventing an additional inverse-SW requirement.
4. Recombine the full signed coin/allocation coefficients before absolute values, and permit the positive proxy constant to depend on fixed (\gamma).

These are sufficient to retain the independent PASS within this audit’s scope. No extra approval condition or new proof obligation is being introduced. This report recommends that the parent treat the entire nonreal-mode bridge as **one additional substantive advance**, with the stated conditional-on-corpus and finite-search qualifications. It does not enact acceptance.

No MathDB ranking, importance score or featured status was observed or claimed in this audit. The named remaining-problem connection and the explicit mathematical improvement suffice for the qualitative significance assessment. No independent upstream validation, formal proof, human peer review or worldwide first-priority certification is claimed.

## 6. Evidence, seals and reproducibility

All newly written evidence is confined to [sources/i10_complex_modes_novelty_r3](../sources/i10_complex_modes_novelty_r3/) and [experiments/i10_complex_modes_novelty_r3](../experiments/i10_complex_modes_novelty_r3/), plus this report. No candidate, shared index, accepted finding or other project was edited; no agents, staging or commits were used.

* [Input manifest](../sources/i10_complex_modes_novelty_r3/input-manifest.json): initial identities of the sixteen principal local inputs, including the complete tree and candidate.
* [Retrieval manifest](../sources/i10_complex_modes_novelty_r3/retrieval-manifest.json): fresh immutable raw URLs, UTC retrieval times, SHA-256 and matching Git blob hashes for 36 selected pinned files.
* [Literature manifest](../sources/i10_complex_modes_novelty_r3/literature-manifest.json) and [additional literature](../sources/i10_complex_modes_novelty_r3/literature-additional.json): exact primary URLs, successful PDF/text hashes, retrieval times and failed-access records. Downloading a file does not itself mean it was semantically read.
* [Inspected ranges](../sources/i10_complex_modes_novelty_r3/inspected-ranges.json) and [sealed range records](../sources/i10_complex_modes_novelty_r3/range-seals.json): source locations actually read, using Python `splitlines()` for numbering (PDF form feeds can make these differ from `sed` line numbers). The latter also records the complete required local readings performed before the range-logging helper was introduced. Two Timofeev pages were visually inspected.
* [Research log](../sources/i10_complex_modes_novelty_r3/research-log.json): bounded query record, version checks, relevant discoveries, limitations and saved search responses. Irrelevant search hits were not treated as mathematical sources.
* [Dependency seal](../sources/i10_complex_modes_novelty_r3/dependency-seal.json), [artifact seal](../sources/i10_complex_modes_novelty_r3/artifact-seal.json), and [validation](../sources/i10_complex_modes_novelty_r3/validation.json): local dependency identities, inherited manifest verification, report/evidence identities and final integrity checks. The artifact seal excludes itself and the final validation file to avoid circular hashes.

The inherited proof audit’s 90 input and 30 artifact records, and the 38 i07 + 11 candidate + 14 r2 pinned-file records, are checked for identity in the final validation. Those checks do not repeat the parent’s mathematical diagnostics or turn the accepted upstream statements into experimentally proved results. The only new mathematical diagnostics here are the exact logical-reduction checks described above.
