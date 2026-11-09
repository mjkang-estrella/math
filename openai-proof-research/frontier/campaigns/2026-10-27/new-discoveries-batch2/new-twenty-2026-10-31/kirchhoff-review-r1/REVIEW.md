Independent adversarial review of MathDB 349441

Recommendation: HOLD for campaign acceptance. A QUALIFIED_PASS; B PASS with explicit minimality limits; C PASS; D HOLD; E QUALIFIED_PASS conditional on novelty. This review grants no credit and changes no shared ledger.

The 11-vertex graph K6 with path 0–6–7–8–9–10 refutes both source algebraic orderings. The spectral failure survives independently of the source's incorrect identification of a Moore–Penrose inverse with a similarity-transformed diagonal pseudoinverse. This is a substantive candidate, but absence of a verified earlier refutation is not a novelty clearance.

A. Source fidelity

I read the supplied arXiv v2 body, MathDB raw record, root ruling, formal definitions and statement correspondence; I also retrieved the live arXiv v2 HTML and the published JMAA article from the authors' institute. The journal copy retains the relevant inconsistency and Conjecture 4.13. It is JMAA 507 (2022), 125728, not an MMNP paper. The denied MMNP route concerns a later paper and was not retried.

For unweighted finite simple connected graphs, (3.8) specifies Lα = diag(cα) − K^α A K^(−α), with cα(i) = sum over neighbors j of (d_i/d_j)^α. The two biases are α = ±1; α = 0 is the ordinary Laplacian. Definition 4.1 is a physical potential difference per imposed current; Lemma 4.2 (4.3) instead specifies the Moore–Penrose expression Xii + Xjj − Xij − Xji. Definition 4.5 sums this expression over unordered pairs. Lemma 4.6 asserts the incompatible eigenvalue expression n sum over nonzero eigenvalues of 1/ρ. Conjecture 4.13 asserts the chain R1 ≥ R0 ≥ R−1 with equality iff regular. The supplied MathDB record reproduces that chain and its computational motivation.

The physical interpretation fails before any ordering can be evaluated: w_i = d_i^(−2α) satisfies wᵀLα = 0, since w_i(d_i/d_j)^α = (d_i d_j)^(−α) is symmetric. Thus LαV = I(e_v − e_w) with nonzero I requires w_v = w_w. The witness has degrees (6,5,5,5,5,5,2,2,2,2,1), so it has incompatible pairs. For instance at α = 1, w_0 − w_10 = −35/36. This obstruction concerns the paper's own equation (4.7), without assuming that its other physical current axioms are consistent. No all-pairs physical index is thereby defined. I agree with the root that the two algebraic readings are the operational review targets. I do not claim refutation of every conceivable repaired physical or directed-resistance model.

My code gives an especially decisive fidelity check. K4 with one pendant vertex has MP values R−1 = 62227/13000, R0 = 17/2, R1 = 33856/4317. Its spectral values are 5695/1144, 17/2, 2696/201 respectively. Consequently the MP ordering already fails at n = 5, within the claimed experiment. The source's report cannot be an accurate exhaustive computation of its literal MP definition. Independent exact checks on the McKay connected graph datasets give:

| Order | Connected graphs | MP ordering failures | Spectral ordering failures |
| --- | ---: | ---: | ---: |
| 5 | 21 | 2 | 0 |
| 6 | 112 | 10 | 0 |
| 7 | 853 | 56 | 0 |
| 8 | 11117 | 545 | 0 |

There were no violations of the separate equality-versus-regularity test in these datasets. The total is 12103 connected graphs. This is strong independent evidence that the authors computed the spectral reading. Their code was not recovered, so identifying the exact implementation remains an inference. The statement that their data supports the literal MP reading is untenable.

The Lean `degree`, `weight`, `laplacian` and `laplacian_source_formula` agree with (3.8). Integer powers on positive connected degrees are valid; possible defaults at isolated vertices are irrelevant at n ≥ 2 and connectedness. `Penrose` has all four conditions, including both transpose conditions. `GroupInverse` has AXA=A, XAX=X and AX=XA. `pairIndex` uses both distinct off-diagonal entries; `spectralIndex` is n times trace. `Conjecture` uses selectors whose zero defaults are bypassed by proved witness certificates. `LiteralConjecture` explicitly quantifies over inverse data. Uniqueness means the existential choice cannot select a different numerical value to evade the violation. The real endpoints use this literal formulation, with exact rational scalar extension.

The equality condition is stated separately for each bias in Lean. Any ambiguity about simultaneous equality in the prose is immaterial to these endpoints: the proofs contradict the ordering itself, without using equality. The spectral formalization is the group-inverse trace interpretation authorized in the assignment. There is no formal Lean eigenvalue-to-trace bridge; its ordinary mathematical justification is given below. A claim that the endpoints formally identify all physical and spectral definitions would overstate the result.

B. Independent exact mathematics

`scripts/exact.py` and `scripts/exhaustive.py` are my own Fraction-based arithmetic and graph6 parser. They import no candidate calculation or certificate code and use no floating point. Full L−1, L0, L1, MP and group matrices are saved in `outputs/witness-exact.json`; the 5-vertex matrices are in `outputs/minimal-MP-certificate.json`.

Construction: with 1 the all-ones column, set P = 1wᵀ/(sum w), G = (L+P)^(−1) − P, U = 11ᵀ/n and W = wwᵀ/(wᵀw). I compute M = (I−U)G(I−W). Local Gauss–Jordan elimination is exact. For each of α = −1, 0, 1 on both displayed witnesses, the code verifies all four Penrose equations for M, all three group-inverse equations for G, and the left-null identity. The construction follows from the one-dimensional left and right kernels; the explicit equations independently validate it on the witnesses.

The exact 11-vertex results are:

| Reading | R−1 | R0 | R1 |
| --- | --- | --- | --- |
| Moore–Penrose pair sum | 21930927/278132 | 370/3 | 515538204/7137235 |
| Spectral / group-inverse trace | 1096887/11036 | 370/3 | 1696684/14035 |

In both rows R1 < R0. For a connected graph, K^(−α)LαK^α is symmetric, and diag(w)Lα is a connected weighted symmetric Laplacian with edge conductances (d_i d_j)^(−α). Hence zero is simple and Lα is diagonalizable with positive nonzero eigenvalues. Its unique group inverse acts by 0 on the zero eigenspace and 1/ρ on each other eigenspace, establishing trace(G) = sum 1/ρ. This explains why the second row tests the actual spectral ordering, without invoking the source's false MP similarity rule.

Minimality: exhaustive labeled connected enumeration at n = 2, 3, 4 (1, 4, 38 graphs) verifies both orderings and equality conditions. The MP counterexample at n = 5 is therefore globally minimal within finite simple connected graphs. The spectral ordering survives the complete connected datasets through n = 8. In the tested family consisting of a clique Kk (2 ≤ k < n) with a pendant path, for every 3 ≤ n ≤ 11, its first failure is n = 11, k = 6. This proves minimality only within that family and tested range. The globally smallest spectral counterexample order is bounded between 9 and 11; orders 9 and 10 have not been exhaustively checked. Do not promote the witness to a globally minimal spectral counterexample.

The graph datasets were obtained from Brendan McKay's public ANU data routes, SHA-256 bound in individual HTTP receipts. The parser checks order, connectivity and expected counts. Exhaustiveness at n = 5–8 relies on the published dataset coverage, whereas the n ≤ 4 enumeration is self-contained. A full n = 9 exact sweep would require much more than the per-process CPU cap at the measured speed; it was not represented as completed.

C. Lean replay and audit

The source-only ZIP matched SHA-256 927d6c3cb8977308a190122f511788bd8606a7cdcbf28ccbc159852b8830ea3c before safe extraction into the initially empty `fresh/`. The extractor rejects absolute paths, parent traversal, symlinks and prebuilt oleans. All five extracted candidate source files match the read-only formal directory byte for byte. Before/after manifests cover 40 required input files and are identical.

Lean reports version 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52. The assignment's pinned read-only mathlib/package cache is used through LEAN_PATH. Basic, Certificates, Graph and RealBridge built with `-j1 -DwarningAsError=true`; all four passed leanchecker. The first checker attempt could not locate `lean` in PATH. I fixed my runner's PATH and reran every checker successfully. That infrastructure failure and its log remain visible.

The original audit passed for all 176 local declarations, including generated declarations. My extended audit also includes my independent `ReviewerClaim`, `reviewer_mp` and `reviewer_spectral`, bringing the total to 179. Each audited declaration records module, full type AST, body via `value? true` (allowOpaque), unsafe/partial flags and transitive axioms. Inductives, constructors and recursors receive their legitimate kernel-kind treatment. All flags are false and all transitive axioms belong to {propext, Classical.choice, Quot.sound}. Full logs are retained, not just endpoint axiom summaries. Source scanning found no forbidden proof mechanism; diagnostic strings mentioning a local axiom are not declarations.

`fresh/formal/ReviewerRestatement.lean` independently spells out the finite connected graph quantifiers, the real inverse conditions, the two biases, the index inequalities and regularity condition, and derives their negations from `KirchhoffReal.refuteMP` and `KirchhoffReal.refuteSpec`. It builds strictly and passes leanchecker. Its axiom lists contain exactly the allowed three.

Negative-control objection: the packet's GroupAsMP and Perturbed examples fail during decidability synthesis, and its WrongMPValue attempt gets stuck in reduction. These failures alone are weak evidence of semantic rejection. My `ReviewerControls.lean` instead proves, using Penrose uniqueness and an explicit matrix coordinate, that GIOne is not MP and that adding the unit matrix entry destroys the MP certificate; it also proves the old numerical value false using the certified pair sum. These proofs build strictly. I additionally retained altered false-claim attempts and their rejection logs; some direct decide attempts still get stuck, so the positive proofs of negation supply the meaningful control evidence.

Every Lean and leanchecker call used the review's own watchdog: two-CPU affinity, CPU limit 120 seconds, wall limit 140 seconds, MALLOC_ARENA_MAX=2 and sampled process-group private RSS cap 6 GiB. No guarded call was killed. Maximum sampled private RSS was 2699993088 bytes; the longest guarded process was the n = 8 exact sweep, 69.60 seconds. The review's heavy processes ran serially. No review-owned jobs remain running.

D. Prior art: HOLD

Search queries, live HTTP receipts, hashes and access failures are retained. Searches for the title, exact conjecture, counterexample, correction and erratum found no verified earlier refutation. This is a bounded negative finding, not proof of novelty. MathDB's empty solution list was not used to clear novelty.

The published article was lawfully obtained from IFISC's author-hosted complete-article link, DOI 10.1016/j.jmaa.2021.125728. Its body retains (3.8), the MP expression, physical equation, Lemma 4.6 and Conjecture 4.13; no correction of the relevant definitions appears there. This closes the predecessor's journal-body gap without retrying ScienceDirect or MMNP.

The later Miranda–Estrada paper, Degree-biased advection–diffusion on undirected graphs/networks, DOI 10.1051/mmnp/2022034, was read in an author-hosted manuscript. I inspected Definitions 2.1/3.1, Proposition 3.9, Theorems 3.11/4.7/4.8, Proposition 4.9 and the conclusions, and screened its complete extracted text for the target terms. Its stationary-state and convergence results do not resolve this index ordering. It adopts the opposite sign convention in its verbal bias labels, which must not be silently carried back into the target.

A Prolegomenon to Differential Equations and Variational Methods on Graphs was obtained from Cambridge. Contrary to the predecessor's identification, its authors are Yves van Gennip and Jeremy Budd, not Mugnolo. The complete extracted text was screened and its relevant literature-overview paragraph and bibliography entry were read: they cite hubs-biased resistance as an example, without discussing this ordering or giving a correction. The local basename `mugnolo-book` preserves the initial identification but is not an authorship claim.

The Chaos 33 (2023) paper Topologically induced suppression of explosive synchronization, DOI 10.1063/5.0142418, was partially read through the beginning of its analytical section using the public primary PDF response. It studies biased Kuramoto dynamics. Later web find operations in one batch produced inaccessible signed-redirect errors. No further requests followed that failure. Its full body is not claimed screened.

A new relevant item is Manuel Miranda's 2026 PhD thesis Diffusion operators on graphs and its applications, supervised by Estrada. Its institute page was read, but its body remains unread: the web tool rejected its size, and a slow public HTTP stream was manually terminated before the wall cap. This is an explicit significant citing/later-literature gap. Mugnolo's later bibliography was searched but no complete current author-wide corpus was screened. No exhaustive citation inventory or complete erratum search is claimed.

Registries were accessed live only through /commits/HEAD. openai/math returned 4eaee87548250b2682affda7d05d947c05554bae, dated 2026-10-30. Omega returned NEW head 74da8002391b09fc1acebaeade18020a4fdc26ac, dated 2026-11-02 07:31:58 UTC, superseding root-known 2bd34aa7fd7676d9c4233eeec266df8aa1541d93. Neither response's changed paths matched the target terms. A HEAD commit response is not the complete current registry. I did not use any other live registry route. Complete semantic registry clearance remains impossible from the allowed route alone and is not claimed.

E. Significance: QUALIFIED_PASS conditional on novelty

The MP-only observation would have weak campaign standing: its minimal example lies within the authors' reported computation and exposes a definitional/implementation mismatch. It should not be credited independently or counted as a second result. In contrast, the spectral ordering passes the reproduced 12103-graph experiment but fails on the 11-vertex witness by an exact, real, kernel-checked inequality under the authorized group-inverse trace reading. That failure is not merely the MP-definition correction. It refutes a substantive universal ordering outside the reported range; producing one parameter instance is sufficient to negate that universal conjecture and is not a separate padding theorem. No known upstream theorem was found that makes this a routine corollary. Nevertheless, unresolved literature and registry coverage prevent an unconditional 'not known' verdict.

Next actions for root: resolve the unread 2026 thesis and remaining citing bodies through lawful permitted sources; determine an acceptable current-registry clearance procedure under the route restriction; present this as one spectral-ordering refutation with a secondary MP correction; retain the n = 9–11 minimality interval; never claim a literal physical-all-pairs endpoint or an audited authors' implementation. Until novelty is cleared, credit stays zero.

Reproduction and evidence

Run scripts from this review directory with `python3 -I`. `scripts/prepare.py` prepares a NEW empty extraction and binds required inputs (do not run over the existing `fresh/`); `scripts/replay.sh`, `scripts/finish-replay.sh` and `scripts/reviewer-checks.sh` document the strict checks. `scripts/exact.py`, `scripts/small-certificate.py` and `scripts/exhaustive.py n` provide independent computations through `scripts/guard.py`. `scripts/finalize.py` checks source identity, immutable input hashes and audit summaries. Full command lines, return codes, timings, sampled RSS and HTTP hashes are under `receipts/`; diagnostic and full declaration output are under `logs/`. All created artifacts remain inside this assigned lane.

Primary retrieval links (review performed 2026-11-02 UTC): [arXiv v2](https://arxiv.org/html/2101.07103v2), [published JMAA author copy](https://ifisc.uib-csic.es/media/publications/publication/c2YCYjD3TBGllC0BLwDVKA.pdf), [later advection author manuscript](https://ifisc.uib-csic.es/media/publications/publication/kvr0RrpqTSSpPppojTB3vg.pdf), [Cambridge citing book](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/63BBE86225E30BBF1ED5C6D0612EC1AA/9781009494656AR.pdf/prolegomenon_to_differential_equations_and_variational_methods_on_graphs.pdf), [2026 thesis listing](https://ifisc.uib-csic.es/ca/publications/diffusion-operators-on-graphs-and-its-applications/). These establish the bounded body-reading claims above, not exhaustive novelty clearance.
