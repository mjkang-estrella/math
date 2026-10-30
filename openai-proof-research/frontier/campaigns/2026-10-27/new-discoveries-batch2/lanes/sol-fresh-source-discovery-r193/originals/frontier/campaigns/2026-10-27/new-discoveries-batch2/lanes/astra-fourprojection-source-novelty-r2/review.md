# Four-projection source and novelty follow-up

Date: 28 October 2026 UTC / 27 October 2026 America/Los_Angeles. Solo review, no children. Candidate identity supplied by the task: `74f23e9fb2`, `root-fourprojection-r1`, 46-entry preliminary hash manifest. This report addresses only the published-body and novelty gates. It does not rerun or extend the earlier mathematical or Lean review.

**Published-body comparison: HOLD. Bounded novelty: HOLD, with substantially improved coverage and no direct prior resolution or complete subsumption bridge found. No acceptance or discovery credit.**

The [preliminary review](../astra-fourprojection-preliminary-review-r1/review.md) remains the source of the ordinary-proof PASS and eight-declaration formal-core PASS. Those findings are not upgraded here to a full formal endpoint. The user-specified pinned Lean/mathlib requirements remain unchanged. No Lean invocation was needed for this follow-up. No candidate, shared file, ledger, or git state was modified.

## Exact question whose provenance remains unresolved

The source is Banica–Nechita, *Flat matrix models for quantum permutation groups*, arXiv:1602.04456v3, Conjecture 6.6, MathDB 332493; published in *Advances in Applied Mathematics* 83 (2017), 24–46, [DOI 10.1016/j.aam.2016.09.001](https://doi.org/10.1016/j.aam.2016.09.001), PII S019688581630077X.

The previously inspected **arXiv** body assumes orthogonal projections P,Q,R,S in M_K(C), PQ=RS=0, ran(P)∩ran(R)=ran(Q)∩ran(S)={0}, and both rank balances

    rank(P)+rank(Q)=rank(R)+rank(S),
    rank(P)+rank(R)=rank(Q)+rank(S).

With D=(P+R)^{dagger/2}, E=(Q+S)^{dagger/2}, the primes are P'=DPD, R'=DRD, Q'=EQE, S'=ESE, using the **positive Moore–Penrose inverse square roots**. The claimed inequality is

    Tr(P'Q') + Tr(R'S') ≤ Tr(PR) + Tr(QS).

The candidate's stronger scope omits both rank balances. Neither removal of the balances nor scalar/polar helper lemmas are additional discoveries. General quantum Sinkhorn convergence is not the candidate's claim.

**I did not obtain an actual published conjecture page.** Consequently I cannot certify its published number, hypotheses, inverse-root convention, rank balances, or survival as an unresolved conjecture in the journal. An unchanged arXiv version, metadata agreement, a later citation, and an open-archive flag do not close this gap.

## Published-body retrieval evidence

Fresh saved HTTP responses, dates, URLs, content types and SHA-256 values are in [retrievals.json](sources/retrievals.json). Files with `.pdf` or `.json` extensions are not necessarily those formats: the log records error responses, and the downloader extracts text only from successful `%PDF` bodies.

| Route | Observed result | Evidential limit |
|---|---|---|
| [ScienceDirect article](https://www.sciencedirect.com/science/article/pii/S019688581630077X) through public web retrieval | 403 | No journal body. |
| [Exact published PDF URL](https://www.sciencedirect.com/science/article/pii/S019688581630077X/pdf), also listed by prior OpenAlex metadata | 403, saved HTML response | No readable PDF or page image. No challenge bypass attempted. |
| [Crossref-advertised Elsevier article API](https://api.elsevier.com/content/article/PII:S019688581630077X?httpAccept=text/xml) | 200, 1,934 bytes | Core metadata only. `openaccess=1` and `openArchiveArticle=true` are not a full-text payload. |
| Same official API, explicit `view=FULL`, plain-text request | 401, 133 bytes, `AUTHENTICATION_ERROR`, `Invalid API Key` | Stopped; no account, key acquisition, or authentication workaround. |
| [OpenAIRE DOI lookup](https://api.openaire.eu/search/publications?doi=10.1016/j.aam.2016.09.001&format=json) | 200, saved complete record | Located DOI, arXiv, HAL and bibliographic links; no additional attached journal copy. |
| Internet Archive public availability query for the exact publisher PDF | 429 | Stopped this route without retry. No archive snapshot was obtained. |
| Exact title/DOI/PII public searches, including author/repository leads | Preprint and bibliographic records | No verified journal body. ResearchGate/preprint renderings were not relabeled as journal pages. |

The following failures are **inherited from the actual preliminary evidence, not presented as fresh retrievals**: [HAL hal-02980384v1](https://cyu.hal.science/hal-02980384v1) had no attached `fileMain_s`, and pointed externally to arXiv; [Nechita's research page](https://nechita.net/research/) linked arXiv and DOI; the linked legacy Banica host refused connection. These routes, together with the fresh official API and OpenAIRE checks, exhaust the specific leads pursued in these two reviews. This is not a claim to have exhausted every legitimate repository or archive on the internet.

The required next evidence remains an authorized copy of the actual journal pages and surrounding definitions/results. Source HOLD is retained without requesting an access bypass or making an exception to the root's acceptance policy.

## Citation-corpus widening

The input was the preliminary review's fixed **26-record** Semantic Scholar corpus, not a new globally exhaustive citation search. Its 13 previously inspected records are inherited explicitly. This pass adds relevant-body reading or screening for **12 of the 13 previously unread records**, corresponding to **nine distinct works**, with duplicate-title/version caveats below. Thus 25/26 records now have at least some body coverage. This does **not** mean 25 complete papers were read, or that all publication versions were compared.

[citation-coverage.json](sources/citation-coverage.json) preserves the prior entries and identifies the new exact versions, pages, scope and limitations. Titles are record labels, not proof of independent works.

1. **Banica, *Quantum permutations and quantum reflections***, [viXra 2009.0045v1](https://vixra.org/pdf/2009.0045v1.pdf), 200-page book. Direct download returned 406, but the public web reader supplied actual PDF body text. I read the displayed statements and surrounding argument for Theorems 12.7, 12.8 and 12.10, and the final Hadamard-model statement 12.21. Theorem 12.7 is equivalence of stationarity, convolution idempotence of the integration state, and idempotence of moment matrices; its proof uses convolution powers. Theorem 12.8 constructs the classical quasi-flat space E_K×L and its stationary measure. Theorem 12.10 identifies a truncated character distribution with a tensor-chain Gram-matrix law. These are not a Moore–Penrose normalization descent theorem. Whole-reader searches for Moore/Sinkhorn did not locate one; Sinkhorn appeared in a bibliography. This is a targeted chapter reading, not all 200 pages. Web screenshot calls produced references only, so **no visual inspection of those screenshots is claimed**. Body excerpts are saved in `web-versions.json`, `web-search-8.json`, `web-search-13.json`.

2. **Banica–Chirvasitu, *Modelling questions for transitive quantum groups***, [1711.03206v5](https://arxiv.org/pdf/1711.03206v5), 14 May 2020, plus the earlier v4 initially obtained. Latest v6 is a withdrawal, 14 November 2020, described on the actual version page as an obsolete old preprint. I checked v5 pp.24–25 and 36, after relevant reading of v4 pp.23–25 and 36. Proposition 8.5 is Idel–Wolf diagonal-unitary Sinkhorn form U=DWE. Theorem 8.7 gives inner faithfulness of universal flat models in specified dimensions. The closing problems concern spectral questions, inner faithfulness, Weyl/Fourier and Hadamard models. None of these statements supplies the four-projection normalization inequality. The corpus's *Stationarity questions for transitive quantum groups* is a title/version lead to this same arXiv family; it is not a second independently read paper or a certification of every historical version.

3. **Banica–Chirvasitu, *Quasi-flat representations of uniform groups and quantum groups***, [1708.09683v3](https://arxiv.org/pdf/1708.09683v3), 31 March 2018. Relevant reading: pp.1–3 and 5–7, especially Definitions 1.4–1.5, Proposition 1.6, Theorem 1.7, Conjecture 1.9 and Propositions 2.1–2.3. Uniform-root spectra, stationary/faithful representation questions and integration moments are the endpoints; the canonical paired-projection trace descent is absent from these results. The corpus's *Faithful matrix models for discrete quantum groups* maps to this arXiv family, rather than supplying an independent fully read source. Historical versions are not all compared.

4. **Banica–Özteke–Pittau, *Isolated partial Hadamard matrices, and related topics***, [1706.00986v2](https://arxiv.org/pdf/1706.00986v2), 7 October 2017. Relevant pp.20–24: Proposition 5.6 relates commuting rank-one projection arrays to pre-Latin structure; Theorem 5.9 is a partial-permutation semigroup description; Theorem 6.1 concerns moments/eigenspaces. The ending conjectures concern isolation and Hadamard extremizers. These results neither normalize arbitrary disjoint projection ranges nor estimate the target trace potential. The rest received a term/theorem inventory screen, not a complete proof reading.

5. **Banica, *Complex Hadamard matrices with noncommutative entries***, [1705.10264v2](https://arxiv.org/pdf/1705.10264v2), 13 July 2017. Relevant pp.7–8 and 10–11 were read, including Theorem 2.6 and **Theorem 3.2 with its full three-part verification**. The latter constructs a magic projection matrix from operator-valued Hadamard entries; unitarity, orthogonality and row/column commutation are hypotheses. The construction uses products of already constrained entries and a scalar 1/N, not positive pseudoinverse normalization of arbitrary four projections. It yields algebraic magic-matrix relations, not the requested trace comparison.

6. **Banica–Chirvasitu, *Thoma type results for discrete quantum groups***, [1705.07050v2](https://arxiv.org/pdf/1705.07050v2), 27 September 2017. Read Proposition 2.6 and its proof pp.6–7 and the quasi-flat concluding discussion pp.15–16. Proposition 2.6 builds an integration-preserving representation from a classical finite-coindex quotient, through a Hopf–Galois/module construction. Theorem 5.6 and Conjecture 5.7 concern stationary quasi-flat models/type-I conditions. Stationarity here means exact Haar integration, not monotonicity of an alternating normalization algorithm. No complete bridge to the candidate was found.

7. **Banica, *Quantum groups from stationary matrix models***, [1604.03756v3](https://arxiv.org/pdf/1604.03756v3), 12 November 2016. Read pp.16–20, including Theorem 5.5 on a classical Latin-square model, Theorem 6.2 on universal flat-model relations and Conjecture 6.3 on inner faithfulness/stationarity. These address representations and Haar integration, not the four-projection objective. Additional theorem/term screening is not claimed as full-paper reading.

8. **Banica, *Deformed Fourier models with formal parameters***, [1603.09433v2](https://arxiv.org/pdf/1603.09433v2), 22 January 2017. Read pp.1–2 and 21, including Theorem 9.1 and the final model discussion, with whole-text relevance screening. Character-law support/atom/asymptotic free-Poisson statements are not positive-polar orthogonalization contractivity.

9. **Weber, *Introduction to compact (matrix) quantum groups and Banica–Speicher (easy) quantum groups***, [actual Springer journal PDF](https://link.springer.com/content/pdf/10.1007/s12044-017-0362-3.pdf), *Proc. Indian Acad. Sci. Math. Sci.* 127(5), 881–933 (2017). The final direct public PDF succeeded (200, 1,461,819 bytes), after landing/IAS leads failed. The actual first page identifies the title, author, journal and date. Read the source-citation passage §7.4.6, printed p.924, and the concluding questions pp.926–928; checked associated representation/category passages and bibliography. The reference to Banica–Nechita [27] recommends matrix models for S_n^+; it does not quote or solve Conjecture 6.6. Relevant body searches located no Sinkhorn/MP/polar normalization theorem. Both duplicate DOI records inherit this **same** partial body reading. An earlier arXiv search lead 1603.09192 was the wrong paper (*Quantum groups with partial commutation relations*); its misleading local filename `weber-introduction.pdf` is retained as retrieval evidence but **excluded** from coverage.

**Remaining unread work:** Stefan Jung's 2019 thesis, *Easy quantum groups: linear independencies, models and partition quantum spaces*, DOI 10.22028/D291-28017. Both [repository landing](https://publikationen.sulb.uni-saarland.de/handle/20.500.11880/27621) and [public thesis file](https://publikationen.sulb.uni-saarland.de/bitstream/20.500.11880/27621/1/thesis.pdf) returned 403; web retrieval also failed. Its metadata/abstract and a related already-read paper are not substitutes for this body. No unread work is declared irrelevant merely from its title.

## Closest newly found matrix-analysis result: actual subsumption test

[Xu–Zhang, *Sharp Frobenius-norm perturbation bounds for subunitary and positive polar factors*, 2507.14940v2](https://arxiv.org/pdf/2507.14940v2), **29 September 2026**, is materially closer than the additional quantum-group surveys. Some search records still describe a July 2025 single-author version; the saved actual v2 is by **Zongben Xu and Teng Zhang**. I read its main statements pp.1–6 and basic convexity/row-column lemmas pp.7–8. Page 3 was locally rendered and visually checked, including Theorem 1.4 and Corollary 1.7. I do not claim a full independent validation of this paper's proofs.

For canonical polar factors X=Q_X|X|, Y=Q_Y|Y|, Corollary 1.7 gives the optimal singular-list-dependent coefficient in

    ||Q_X-Q_Y||_F ≤ C(σ(X),σ(Y)) ||X-Y||_F

for equal rank r, where

    C² = max_(1≤k≤r) 4k /
         [ Σ_(j=1)^(r-k) (σ_j-τ_j)²
           + Σ_(j=1)^k (σ_(r+1-j)+τ_(r-k+j))² ].

The unequal-rank Theorem 1.4 adds the unmatched singular-value terms. These sharp bounds still do not provide a uniform coefficient 1 on the candidate's frame class by direct application.

Here is an explicit admissible specialization demonstrating the obstruction. In C^4 let p=e1, q=e2, r=t e1+sqrt(1-t²)e3, s=t e2+sqrt(1-t²)e4, with 0<t<1; uppercase letters denote their rank-one projections. All original hypotheses, including both rank balances, hold. For X=[p r] and Y=[q s], both singular lists are

    (sqrt(1+t), sqrt(1-t)).

The k=1 term of Corollary 1.7 is exactly 1/(1-t); thus its squared coefficient is at least 1/(1-t), tending to infinity. This is a computation from the displayed theorem, **not a counterexample to the candidate** (these two frames have mutually orthogonal spans, so their normalized cross-overlap is zero). It shows that even this sharp singular-spectrum perturbation theorem loses the structural information needed by the proposed direct route.

There is also an objective mismatch. In the preliminary proof's notation, the target is

    ||K+JKL||_F²/4 ≤ (Tr(A²)+Tr(B²))/2,
    K=U*V, U=X(X*X)^(-1/2), V=Y(Y*Y)^(-1/2),
    A=X*X-I, B=Y*Y-I.

It depends on two normalized frames and their graded cross-overlap. A theorem bounding the movement of a single polar factor in terms of ||X-Y|| does not state this comparison. The entrywise weighted relation coming from PQ=RS=0 is additional data. No substitution eliminating this difference and recovering coefficient 1 was found.

The same paper restates **Kittaneh's coefficient-1 modulus bound**, Corollary 1.23:

    || |X|-|Y| ||_F ≤ ||X-Y||_F   for normal square X,Y.

This is about **positive moduli**, not subunitary polar factors or normalized range frames. The self-adjoint block dilation for arbitrary rectangular matrices gives Theorem 1.22,

    || |X|-|Y| ||_F² + || |X*|-|Y*| ||_F² ≤ 2||X-Y||_F²,

exactly as the paper notes. It does not by itself introduce inverse square roots or bound the desired K+JKL. Theorems 1.5, 1.14, 1.19 and 1.24–1.25 concern positive-factor perturbations, sums, matrix AM–GM or normal-matrix eigenvalue refinements, again different endpoints. The original Kittaneh article was not independently retrieved; this comparison uses the actual Xu–Zhang statements with their attribution, not a claim to have read that original.

Lemmas 2.3–2.4 in Xu–Zhang explicitly recall the standard doubly-substochastic/partial-permutation convex geometry. Row/column mass bounds and polar optimality therefore should not be presented as novel ingredients. The possible contribution is only the complete specific source-question resolution, if all gates are later satisfied. This analysis excludes a **direct** reading/application of the inspected theorems; it is not a proof that every ingenious corollary route is impossible.

The earlier comparisons with 1911.04912, 1608.05811, de la Salle, Li/LAPACK83, Frank–Paulsen–Tiballi, Antezana–Chiumiento and Makarov–Seelmann remain inherited from the preliminary report. They were not needlessly re-reviewed here.

## Older full trureturing checkout

Read-only content searching used the supplied old clone under the previous campaign, not the latest tiny GitHub tree. Reading `.git/HEAD` and its referenced loose ref without invoking git established checked-out branch `dev` at **f8ffe9ed02e01601ed0b43a400ebc1c09cdc6ada**. This establishes the recorded checkout revision; it is not an integrity audit of every working-tree file or every historical commit.

The saved search includes Markdown, Lean, TeX, JSON and text bodies, with case-insensitive Banica/Nechita, exact-source-ID, four-projection, Sinkhorn, and polar/orthogonalization terms. There were no Banica, exact-word MathDB 332493, or arXiv 1602.04456 matches in the saved results. Raw numeric substring hits in unrelated large-number JSON are not exact problem-ID matches. See [trureturing-screen.json](sources/trureturing-screen.json) and the retained raw results.

Two substantive nearby hits were read rather than dismissed by filename:

- `Library/QuantumContext/devos2014scalingunitary.md`: De Vos–De Baerdemacker diagonal-phase unitary scaling and the landscape Ψ=n²-|sum B_ij|². This is a different optimization problem, not paired positive-root projection normalization. Its linked landscape refutation is not asserted to refute or resolve the candidate.
- `Blueprint/D5/S3/Quantum/QuantumChannels/NuclearNormAdditivity.md`: rectangular real polar factors, nuclear-norm duality, weighted rank-one sums, and an equality criterion involving normalized Gram matrices. Its stated normalization is by vector lengths; the endpoint is nuclear-norm additivity. The blueprint supplies no target four-projection trace theorem or complete subsumption bridge.

Other Nechita/projection hits concern different quantum-channel or context problems. This is a bounded content search plus reading of close hits, **not** a replay of the entire repository, a complete theorem audit, or a full-history search. The earlier bounded Ideosphere assessment is inherited, not upgraded to global catalogue clearance.

## Handoff

The searches did not establish that the journal altered the question, nor that a prior result solved it. They also did not establish the contrary. **SOURCE remains HOLD because no actual journal conjecture page was read. NOVELTY remains HOLD**, despite improved citation coverage, because one relevant thesis remains inaccessible, several long works received only targeted reading, historical/published variants were not all compared, and no bounded negative search proves global priority. There is no positive prior-resolution finding justifying NOVELTY FAIL.

All provenance and limits are retained for root review. The next decisive source action is a legitimate journal-body acquisition. A future claimed prior subsumption should identify an actual theorem and provide the full canonical-normalization, hypotheses and coefficient-1 bridge. Formal endpoint completion, literal replay, independent review, paper and deterministic/extracted packet validation remain root-controlled gates outside this assignment. No acceptance/count change is supplied.
