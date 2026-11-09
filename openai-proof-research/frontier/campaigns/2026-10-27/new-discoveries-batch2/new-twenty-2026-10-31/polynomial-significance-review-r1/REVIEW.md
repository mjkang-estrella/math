# MathDB 347913: independent significance and prior-art adjudication

Reviewed 2026-11-01 UTC, working alone. **Recommendation: FAIL the campaign's nonroutine-discovery qualification, on an affirmative routine-adaptation bridge. Actual credit: 0.** This does not reject the mathematical conclusion or the formalization. Root alone accepts; the campaign remains 3/20 beyond 39. The separate fidelity/Lean review was neither polled nor assumed successful.

The decisive new evidence is Marshall and Olkin's actual primary technical report, recovered lawfully from Stanford. Section 4.2, printed pp. 16–18, contains the permutation/prefix-rate transform calculation that the ordinary review had not obtained. It supplies the candidate's central coefficient mechanism directly after a zero-argument limit and incidence substitution. No earlier paper explicitly stating the full hypergraph convexity conjecture as solved was authenticated. The finding here is **routine mathematical subsumption**, not a claim that someone previously announced this exact conjecture's solution.

## Separate verdicts

* Exact source/version: **PASS**. The literal target survives in the published body, without the degree/edge-size limitations of the known partial results.
* Prior art/subsumption: **FAIL qualification**. The full bridge below starts with an inspected, explicitly proved general transform formula from a 1966 primary report. This replaces the prior uncertainty about whether merely recognizing the common-shock model was enough.
* Novelty: **not certified; FAIL as a nonroutine new discovery under the campaign rule**. A newly stated application or first formalization could remain worthwhile, but is insufficient for this campaign. No worldwide-priority assertion.
* Mathematical significance: solving the full published problem is substantively stronger than the inspected limited-parameter results. **FAIL the additional requirement of a nonroutine coefficient mechanism beyond existing general formulas**. The rejection rests on the exact formula and bridge, not shortness or classical ingredients alone.
* Lean status: read-only scope review; no rebuild or independent axiom audit here. The author's 205-declaration/18-build/18-checker report remains author-reported evidence.

## Exact source and statement

Read the literal r40 raw/347913.jsonl, PROOF-ATTEMPTS.md, both actual source text bodies, ordinary review's 347913 section and review.json, and Source/Identification/Endpoint.lean in the frozen r3 candidate. The endpoint is `PolynomialConvexity.source_conjecture : SourceConjecture`. Its source definitions genuinely sum over functions Fin d → Edge n L, with inclusive prefix unions, so repetitions are admitted. It does not define the polynomial by a moment.

The source is Brosch–Laurent–Steenkamp, arXiv:2009.04510v1, Eq. (2), Section 3 Conjecture 1. The published SIAM J. Optim. 31(3) (2021), 2227–2254, DOI [10.1137/20M1369592](https://doi.org/10.1137/20M1369592), moves this to Eq. (1.1), Section 4 Conjecture 1. Its primary body is already cached at r40/sources/published-brosch.txt, not inferred from metadata. Both ask for all integers n,L,d≥2, E every L-subset of [n], and convexity on x≥0, Σx=1 of

\[
f_d(x)=\sum_{(e_1,\ldots,e_d)\in E^d}\Bigl(\prod_i x_{e_i}\Bigr)\prod_{j=1}^d |e_1\cup\cdots\cup e_j|^{-1}.
\]

There is no distinctness requirement and no multinomial coefficient in this definition. The final-union-only polynomial p_d is different; its convexity does not clear this question. The barycenter/balance consequence is weaker than full convexity. When L>n, E is empty and the sum-one simplex is empty; this boundary is vacuous and requires no value for 1/|E|. Nonempty edges are essential to the lifetime representation; L=0 is outside scope.

Identification.lean proves an actual integral equals the symmetrized coefficient. Endpoint.lean expands it to d!f_d and uses convexity of nonnegative powers before restricting to the simplex. I independently checked that ordinary chain's scope and normalization; I did not replay each Lean proof. The new source finding concerns precisely that same symmetrized coefficient, not an unrelated exponential law.

## A. Recovered primary formula and complete subsumption bridge

**Authenticated body:** A. W. Marshall and I. Olkin, *A Multivariate Exponential Distribution*, Technical Report No. 23, Department of Statistics, Stanford University, March 1966. Title/authors/report number/date are visible in the scanned title pages, and agree with the institutional metadata. [Stanford record](https://purl.stanford.edu/kb905zm7154); [public PDF](https://stacks.stanford.edu/file/kb905zm7154/kb905zm7154_OLK-NSF-23.pdf). HTTP 200, retrieved 2026-11-01 12:25:20 UTC, SHA256 **fc78f4f0967db8fee56f9247f155a9468d8ca899acdd6048206e126deb358f74**. The PDF has 29 scanned pages; printed pp. 14–18 are PDF pages 16–20. Those five pages were rendered and actually read at useful resolution. The report is an earlier primary version, **not an independently verified copy of the typeset 1967 JASA article** (DOI 10.1080/01621459.1967.10482885). The latter full body remains unread. The report's digital record publication date is 2025-08-11; the report itself is dated March 1966. Either date precedes this candidate. No claim of byte/label equality between report and journal is needed for this objection.

In modern subset notation, the report gives the following. For q components and rates λ_S indexed by nonempty S⊆[q], its survival function is

\[
\bar F(t)=\exp\{-\sum_{S\ne\varnothing}\lambda_S\max_{i\in S}t_i\}.
\]

This is report Eq. (4.3), printed p. 15, from the shock derivation on p. 14. Write
\(g_A=\sum_{S:S\cap A\ne\varnothing}\lambda_S\).
The report defines these g parameters on p. 17. Section 4.2 does **not** merely assert existence of an mgf: it computes the modified Laplace transform

\[
\phi(s)=\mathbb E\prod_{i=1}^q(1-e^{-s_iX_i})
=(\prod_i s_i)\sum_{\pi\in S_q}\prod_{j=1}^q
\left(g_{\{\pi(1),\ldots,\pi(j)\}}+\sum_{k=1}^j s_{\pi(k)}\right)^{-1},\qquad s_i>0. \tag{MO}
\]

The integration-by-parts formula is labelled (4.6), printed p. 17. The iteration and final permutation formula are unnumbered on p. 18. They explicitly use all q! descending coordinate regions. The same page gives the independent-exponential minimum representation. This is the actual proof body and formula; it is not an abstract or a secondary citation.

Here is the complete specialization.

1. Fix any ordered tuple (e_1,…,e_d) of nonempty edges of any finite hypergraph. Use **q=d labelled components**, even if edges repeat. For each vertex v set I_v={i:v∈e_i}. For nonempty S⊆[d] set λ_S=#{v:I_v=S}; vertices with I_v empty do not enter. Independent rate-one vertex shocks with equal I_v can be grouped into a shock of rate λ_S, since the minimum of those independent exponentials has that rate. Then X_i=min_{v∈e_i}T_v, with the same T_v shared among all components. For every nonempty A,
   \[
   g_A=\sum_{S:S\cap A\ne\varnothing}\#\{v:I_v=S\}
   =\bigl|\bigcup_{i\in A} e_i\bigr|>0.
   \]
   This is a direct incidence-count identity, valid for all d and L, not the p_d coefficient.

2. Some λ_S vanish, and repeated edges can give identical components and a singular law. No unmentioned positive-density hypothesis is required. Even if the report's parameter convention is read as strictly positive λ_S, replace every λ_S by λ_S+ε. Couple the extra shocks as U_S/ε, with independent rate-one U_S. Each component X_i^ε=min(X_i,min_{S∋i}U_S/ε) increases almost surely to X_i as ε↓0. Formula (MO) passes to this boundary by bounded convergence on its left and continuity on its right: g_A becomes g_A+ε(2^d−2^{d−|A|}) and every original g_A stays positive. This closes the entire zero-rate/singular/repeated-component issue with a finite-dimensional parameter limit.

3. In (MO) divide by ∏s_i and set every s_i=h>0. As h↓0, (1−e^{-hX_i})/h increases to X_i. Monotone convergence and the finite positive denominators give
   \[
   \mathbb E\prod_{i=1}^d X_i
   =\sum_{\pi\in S_d}\prod_{j=1}^d g_{\{\pi(1),\ldots,\pi(j)\}}^{-1}
   =\sum_{\pi\in S_d}\prod_{j=1}^d
   |e_{\pi(1)}\cup\cdots\cup e_{\pi(j)}|^{-1}. \tag{*}
   \]
   The right side is finite, so this argument itself establishes the needed mixed-moment finiteness. It imports the report's proved chamber calculation; there is no new all-degree chamber/Jacobian mechanism left to discover. For an all-equal tuple it gives E[Z_e^d]=d!/|e|^d, as required.

4. For the complete L-uniform hypergraph take one common vertex-shock model and define Z_e=min_{v∈e}T_v for all edges simultaneously. Expand the finite power (Σ_e x_eZ_e)^d as the sum over **all ordered tuples with repetition**. Equation (*) gives each term's integral. For each fixed permutation π, e↦(e_{π(1)},…,e_{π(d)}) is a bijection of E^d, and ∏x_ei is unchanged. Thus each of the d! permutations contributes exactly f_d(x):
   \[
   \mathbb E(\sum_e x_eZ_e)^d=d!f_d(x).
   \]
   No stabilizer quotient or division by edge multiplicities is allowed. For signed x the finite mixed moments also justify absolute integrability and termwise integration, though convexity only needs x≥0.

5. For x,y≥0 the corresponding random linear forms are nonnegative. Apply convexity of u↦u^d on [0,∞) pointwise to θx+(1−θ)y, integrate, and divide by d!>0. This proves convexity on the full nonnegative orthant, hence on the source simplex, for every n,L,d≥2. Empty E is handled directly as above. This is a complete bridge to the exact source assertion.

Consequently this is more than recognizing an old distribution: **the inspected old proof already evaluates the exact integral into the exact prefix-rate permutation product**. Incidence specialization, a zero-argument limit, finite tuple reindexing and scalar power convexity complete the application. Under the explicit exclusion of routine adaptations, I recommend no discovery credit. The conclusion may be useful and may not have been explicitly observed by the source authors, but their retained conjecture cannot override this affirmative subsumption bridge. Formalizing the old general calculation is substantial implementation work, not independent evidence of mathematical novelty.

## B. Source successors and concrete exclusions

Reused original bodies and hashes rather than copying evidence trees. See read-sources.json and frozen-inputs.json for original paths/hashes, plus local receipts for newly downloaded bodies.

* **Polak, arXiv:2104.08264**, Theorem 1.1 and the fixed-degree symmetry/PSD procedure: L=2,d≤9, all n. It does not cover arbitrary d or L. The file named polak-published in the earlier review is byte-identical to that preprint; it does not independently verify the typeset 2022 SIAM publication. The source's published discussion also mentions an earlier d≤8 stage. Neither statement changes full scope.
* **Brosch thesis**, Chapter 5, definitions and Conjecture 5.17 with surrounding Hessian discussion: retains all n,L,d≥2 convexity and mentions limited-degree progress. This is positive evidence of the target's scope, not an absence-of-prior-art proof.
* **Cardinaels–Borst–van Leeuwaarden, arXiv:2111.05777**, coefficient definition, Theorem 1, Lemma 3 proof and Corollary 1 discussion: the queueing coefficient is the ordered prefix-union coefficient in the L=2 model. Lemma 3 obtains a light-traffic expansion; Corollary 1 uses convexity only for q≤9 and the text discusses numerical evidence beyond that. Neither a full convexity theorem nor (*) is supplied in those inspected passages. The preprint and journal citation are two of the earlier four DOI-linked index records, not two independent full general proofs.
* **Previously unread quantum citer:** Crossref DOI 10.1109/TIT.2025.3589660 identifies Chee–Ta–Vu, *An Efficient Parameterized Algorithm for Computing Quantum Channel Fidelity via Symmetries Exploitation*, IEEE Trans. Inf. Theory 71(9), 7003–7015 (2025). Recovered their author preprint **arXiv:2308.15884**, under the title *Efficient Approximation of Quantum Channel Fidelity Exploiting Symmetry*: v3 dated 21 March 2024, SHA256 25c2cbcf3b4410d7754fb26848925c518b2dbe4953f9fc376db781173e18f3d4; current v4 dated 19 April 2026, SHA256 ada80f20dfdf4d0df1a0bbb507b0321239c1e9e8955644f19be5aafa6a0b1619. Authors, channel problem and citation [BLS21] agree. Read main theorem, actual Section 3 reduction statements and proof context, and the [BLS21] citation occurrence. In v4 Theorems 3.4 and 3.6 concern polynomial-size equivalent channel SDPs and computing their block transformation; the proof uses representation-theoretic block diagonalization. The BLS21 citation is in the related-work list of symmetry applications. Those theorems take a channel, dimensions and hierarchy level as input and supply an algorithm, not positivity of every source coefficient Hessian or an exponential moment representation. Applying a generic PSD block equivalence still requires establishing PSD of this source's blocks. Thus **these inspected author versions do not subsume the full conjecture**; this is a primary-body scope bridge, not a title exclusion. The separately typeset 2025 IEEE body remains unverified; title change and bibliographic identification do not certify every version identical.
* **Additional targeted later hit:** Moradi Daleni, *Optimizing Hypergraph for Polynomials Modeling with Redundancy Scheduling*, Ann. Optim. Appl. 1(1) (2025), 41–49, DOI 10.48314/anowa.v1i1.38, publisher PDF HTTP 200, SHA256 fe89c5f4fe0c58d19f7912070a2f70bd204da304d34f946af245595205e6aca5. Read definitions (5)–(6), Conjecture 1 and the surrounding claims, and inspected subsequent section structure. Pages 42–44 explicitly retain only d=2 and d=3,L=2 results for f_d and distinguish the general p_d claim. Subsequent displayed lemmas concern observer/control inequalities, not the required all-degree coefficient identity. This body supplies no full bridge; I do not endorse its other assertions.

Targeted searches also included higher mixed moments of the common-shock law and order-independent queue/balance/partition-function moment representations. Search snippets were navigation only; no unseen result is treated as excluded. A Steenkamp thesis download at https://ir.cwi.nl/pub/33411/33411D.pdf stalled during body reading and was interrupted; no complete body or theorem from it is relied on. Its abstract/search description is not clearance. Citation indexes, alternate titles, inaccessible versions and unindexed work remain finite-screen limitations. None can rescue novelty from the explicit older formula already recovered.

## C. Live registries, history and limits

Live GitHub HTTP receipts at 12:24 UTC authenticate OpenAI/math HEAD **4eaee87548250b2682affda7d05d947c05554bae**, unchanged from the supplied check, and Omega HEAD **cc684e6326490f9173bfefcadb0294ee6ccbb0b5**, changed from 2ca21e959611edb7fe34b99383bc0bef1283fcc4. See openai-head/omega-head receipts and bodies. Used the current complete OpenAI preprint subtree cached in misere-significance-review-r1/openai-preprints-tree.json: tree 3f56f68a176b4494c346091ea0a319651bc217ec, 13,578 entries, truncated=false, SHA256 6ac178a0ebcece8f2c2c9aa1c22022068110bbdae4bb3d1ffa9f1b693b9e0305. The older project sources/preprints-tree.json is a different 13,223-entry snapshot and was not mistaken for the live catalogue. Exact-ID/source-alias path screening returned no direct match; paths alone do not certify unrelated bodies excluded.

Omega's previously cached complete combinatorics source/blueprint subtrees were examined with their hashes (recorded in read-sources.json). The live compare endpoint from the supplied head to the new head gives 31 commits but **300 file entries**, a GitHub comparison cap: it is not a full repository clearance. The visible mathematical changes concern nSSP minimum arcs, quantum power means and interval compactness; unrelated proofs were not audited. No new Omega hypergraph-convexity proof body was authenticated. Unscreened subtrees, capped comparison contents and indirectly named proofs remain explicit limits. No truncated root recursive tree was treated as complete. No current MathDB/Palomar clearance is claimed; the inherited 403s were respected without retry. Broader public search supplied no further authenticated exact subsumer, but is not an exhaustive registry audit. Since an affirmative older formula already defeats the campaign qualification, these limits cannot support a PASS and are not concealed as clearance.

Read batch prior-campaign-context.json, both ledgers and ordinary review's actual history scan/old-hold context. accepted-scope-comparison.json records the 39 historical plus 388087,333569,347712 source scopes. The common-shock prefix polynomial is different from Kiraly's full-blocker choice-map counterexample, the Petersen–Wilson entropy-series/Markov local intricacy question and the Latin finite-field partition counterexample. The historic polynomial-root, analytic-inequality, graph-invariant and moment-related families have different literal source objects and conclusions; no accepted source alias is this BLS conjecture. This is no new credit for the r40 ordinary mechanism, its successive Lean continuations, helpers or the orthant/general-hypergraph extension. Earlier holds were proof/qualification gaps rather than acceptance. The new rejection reason is the authenticated general transform bridge, not a relabelled old unresolved objection.

## Evidence and execution boundary

All 130 frozen bindings matched before work (bindings-before.json) and after (bindings-after.json); the ZIP hash is the specified 859afaf1d4cc7799f6e6559052766bdf0c81ca192d322b93b860ac1704aa5681. Original evidence remains in place. New response bytes, dated URL/status/SHA256 receipts, rendered report pages and the fetch script live only here. `mo-report.txt` is empty apart from form feeds because the PDF is scanned; formulas were read visually, not hallucinated from failed extraction. mo-detail-16.png through mo-detail-20.png identify the actual pages relied on.

Public reads only; no git, Lean build, children, author/historical/shared edits, publication/uploads, messages or browser tabs. Fetches were serial, with 25-second socket timeout, 90-second CPU/2-GiB address-space limits, and outer finite wall timeouts; one stalled read was explicitly interrupted and its session terminated. PDF rendering/extraction ran serially with finite timeouts. No CPU-heavy parallel work was launched. Basic read/hash commands were small synchronous processes, not independently sandbox-audited resource runs. No jobs remain at handback. Access failures and incomplete bodies are not used as evidence of absence. The final recommendation is limited to this campaign's substantive-credit rule; it does not invalidate a correct Lean proof or certify worldwide bibliographic priority.

Final live-head recheck immediately before adjudication: 2026-11-01T12:30:46.350473+00:00 HTTP 200 https://api.github.com/repos/openai/math/commits/HEAD; 2026-11-01T12:30:49.429528+00:00 HTTP 200 https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD. Both heads remained as reported above.
