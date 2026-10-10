# Final prior-art and significance audit: variable-channel four-state capacity

**Verdict: recommend acceptance as one substantial conditional deduction, with the novelty confined to the uniform four-state sufficiency bridge.** The exact theorem is not stated in the strongest applicable pinned companions or the primary literature inspected here. Its full range is not obtained by the standard subdivision, common-channel simulation, scalar-capacity substitution, or terminal-erasure reductions examined below. This recommendation rests on those mathematical comparisons, not on an unsuccessful keyword search. The capacity formalism, series laws, necessity construction, and warning that unweighted capacity fails near perfect transmission have substantial precedents and should not be presented as new discoveries.

This is a bounded significance recommendation, not a worldwide-priority certificate. The independent proof review is PASS; I found no new substantive mathematical objection. Both reviews remain conditional on the accepted pinned corpus. There is no human peer review or Lean certification of this deduction. **The parent alone assigns an R-number, integrates the result, and changes the accepted count; this review leaves R006/R008 and the count of two unchanged.**

Audit date: 2026-10-08 America/Los_Angeles; retrievals occurred on 2026-10-09 UTC. No agents, staging, commits, shared-index edits, candidate edits, or edits to other reviewers' artifacts were performed.

**1. Exact audited claim and input identity.** I read the complete candidate and complete independent round-2 proof review, rather than treating the task summary as evidence. The candidate hash is `4220b53ff1d80ba82795c56cc075944f9ed011ae13cb7be976e1dd4e8c037f6b`; the proof-review hash is `f271e483db49d17b14bab301c71979d47894d99cc82858b35eff89f9d2fc745f`. Both are snapshotted in the assigned source directory. The [input manifest](../sources/i08_variable_capacity_novelty_r3/input-manifest.json) also hashes `AGENTS.md`, `sources/upstream.json`, `sources/CONTENTS.md`, the complete `sources/preprints-tree.json`, and `frontier/TEN-FINDINGS.md`.

The claim concerns a deterministic infinite rooted tree with at most a fixed finite B children at every vertex, a uniform four-state root, independent edge transmissions conditional on their parent spins, and observed tree and parameters. Every edge has

\[
P_{\lambda_e}=\lambda_e I+(1-\lambda_e)\mathbf1\mathbf1^{\mathsf T}/4,
\qquad 0<\lambda_e\le1.
\]

Writing \(r_e=\lambda_e^2\) and \(R_v=\prod_{e\in[\rho,v]}r_e\), reconstruction from depth-n spins means a strictly positive limiting expected posterior TV distance from the uniform prior. The theorem equates this to a nonnegative conserved flow of **finite positive mass** with

\[
\sup_{\xi\in\partial T}\sum_{e=(v,w)\in\xi}
(1-r_e^2)\frac{\theta(e)^2}{R_w^2}<\infty.
\]

Normalization to potential at most one uses homogeneity; zero potential is allowed, and capacity can be infinite. There is no uniform separation from either zero or one. Zero edge parameters, antiferromagnetic channels, unobserved environments, and an a priori uniform advantage over all trees are not asserted.

**2. Complete-inventory corpus comparison.** The pin is `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The full JSON inventory was parsed in its entirety: **13,223 entries, 749 first-level preprint directories, `truncated: false`**. The catalogue's own headline says 719 manuscripts; it was not used as a substitute for the complete inventory. [inventory-screen.json](../sources/i08_variable_capacity_novelty_r3/inventory-screen.json) retains all manuscript-directory names, the screening expression, and all matching directories. The search covered Potts, Ising, reconstruction, broadcasting, capacity, trees, entropy, information, and channels; unrelated algebraic reconstruction, planar Ising, quantum-channel, metric-tree and PDE-capacity titles were separated by their catalogue scope. This is an inventory/catalogue-wide screen with detailed reading of the applicable sources, not a claim to have read every manuscript in the corpus in full.

I freshly retrieved **41 source files** from immutable raw GitHub URLs in the four closest families. Every fetched file's Git blob SHA-1, including the Git header, equals its entry in the complete inventory. SHA-256, byte length, exact URL and local path are retained. The pertinent statements are:

- **Capacity companion:** [A Capacity Criterion for Four-State Potts Reconstruction on Trees, `build/main.tex`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Capacity-Criterion-for-Four-State-Potts-Reconstruction-on-Trees-October-5-2026/build/main.tex), read in full. `thm:main` fixes one \(0<\lambda<1\), a deterministic tree with at most B children, and the same posterior-TV reconstruction quantity. Its potential is \(\sup_\xi\sum(\lambda^{-2|e|}\theta(e))^2\). `prop:companion`/`eq:moment-saving` supplies the law-class input. `lem:local-moments` assumes one input smoothed by that fixed channel. `eq:denominator` uses \(Z\ge1-\lambda\); `eq:uniform-loss-bound` sums a geometric kernel and divides by \(1-\lambda\). This is the strongest direct predecessor. Its main-file SHA-256 is `0e73632ec22fb64a26e0d0cda579d7b670bf3a75379b1b2747e0a919a6ad2ffd`, Git blob `90c4681d47201bea1ecc09340035003f20a50378`.
- **Four-state threshold companion:** [`01-introduction.tex`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Reconstruction-Threshold-for-the-Ferromagnetic-Four-State-Potts-Model-October-5-2026/build/sections/01-introduction.tex), `thm:main`, concerns one common \(\lambda\in[0,1]\), regular d-ary trees with integer d≥2 and observed Poisson(d) trees with d>0, with unconditioned averaging. It proves nonreconstruction for \(d\lambda^2\le1\). [`03-cone.tex`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Reconstruction-Threshold-for-the-Ferromagnetic-Four-State-Potts-Model-October-5-2026/build/sections/03-cone.tex), Proposition 3.2, `prop:cone-closure`/`eq:moment-saving`, really does allow every channel parameter in [0,1], finite conditionally independent products, and observed input-independent mixtures. This stronger local scope is already upstream; using different edge parameters does not invent a new preserved class. `02-experiments.tex` and `04-tree-decay.tex` were also read. The latter's `prop:tree-recursion` has identical-distribution child inputs and does not state the proposed arbitrary-tree converse.
- **Three-state companion:** [`01-introduction.tex`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-exact-reconstruction-threshold-for-the-three-state-symmetric-channel-September-25-2026/build/sections/01-introduction.tex), `thm:threshold`, covers one common \(-1/2\le\lambda\le1\), regular b≥2 and observed Poisson d>1, and exact \(d\lambda^2>1\). Its `cor:sbm` is a three-community consequence. The potentially suggestive `05-weighted.tex`, `wei:exclusion`/`wei:identities`, concerns weighted logarithmic functionals at negative homogeneous equality, not variable-resistance tree capacity. Neither statement subsumes a four-state variable-channel equivalence.
- **Closest Ising corpus companion:** [`01-introduction.tex` of The sharp factor-of-IID threshold for the free Ising model on regular trees](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/build/sections/01-introduction.tex), `thm:main`/`thm:sharp`, concerns homogeneous binary free states and automorphism-equivariant factors on regular trees. Generating a whole spin law from IID labels is a different quantity; this source does not supply the missing four-state posterior comparison.

I accepted these source premises as instructed. Downloading certificate sections for provenance was not an upstream truth audit.

**3. Pemantle–Peres is a close precedent, including the near-perfect obstruction.** In [Pemantle–Peres, *The critical Ising model on trees, concave recursions and nonlinear capacity*, arXiv:math/0503137v3](https://arxiv.org/abs/math/0503137v3), equations (2.1)–(2.3) define nonlinear capacity using arbitrary nonnegative edge resistances and path exponent p−1. Theorem 2.1 treats free-boundary binary reconstruction with p=2 and resistance \(\prod\tanh(\beta J)^{-2}\); Theorem 2.2 treats plus-boundary magnetization with p=3 and resistance \(\prod\tanh(\beta J)^{-1}\). Both assume an infinite locally finite leafless tree and (1.1), \(0<J_{\min}\le J_e\le J_{\max}<\infty\). Lemma 3.1, Theorem 3.2 and Corollary 3.4 relate capacities to scalar recursions with uniform comparison constants. End of §4 removes the lower interaction bound by subdivision, but explicitly demonstrates failure of the unweighted criterion when biases tend to one. The relevant PDF page 14 was visually checked and retained.

Thus it would be inaccurate to describe this literature as constant-channel only, or to advertise the candidate's ray example as discovery of an unsuspected defect in earlier capacity theory. That defect and the degree-two subdivision mechanism were already recognized.

The quantities nevertheless differ. Using bias \(\lambda_e\) in the Ising free state gives a path potential linear in flow, with coefficient \(R_w^{-1}\), rather than the candidate's squared-flow potential. Using bias \(r_e\) in the Ising **plus** state aligns the exponent and the unweighted resistance on a compact parameter range, but changes the observable from an average over broadcast posteriors to response under an all-plus boundary. There is no probabilistic identification between those two experiments. Substituting \(r_e\) for the Ising bias does not prove the four-state theorem.

More explicitly, set

\[
\rho(e)=\frac{\sqrt{1-r_e^2}}{R_w}.
\]

The candidate's capacity is exactly a conventional p=3 tree capacity with these resistances (with the harmless ≤1 normalization covering an all-zero-resistance ray). This **is not a new kind of capacity**. If c_v denotes capacity below v using the absolute resistances, the ordinary parallel/series laws give

\[
c_v=\sum_w\frac{c_w}{\sqrt{1+\rho(v,w)^2c_w^2}}.
\]

Putting \(z_v=c_v/R_v\) yields

\[
z_v=\sum_w\frac{r_ez_w}{\sqrt{1+(1-r_e^2)z_w^2}}.
\]

This computation is standard deterministic potential theory. The nonstandard step is comparing actual four-state boundary experiments with this recursion in both directions, especially constructing informative experiments from a capacity flow uniformly when \(\sup_e\lambda_e=1\). A theorem about scalar labels does not supply that comparison merely by naming the same resistances.

**4. Other primary literature and the same-quantity check.** The retained PDFs and their hashes are in the [literature retrieval manifest](../sources/i08_variable_capacity_novelty_r3/literature/retrieval-manifest.json). Versions below are the versions actually read, with theorem labels in those versions.

- [Evans–Kenyon–Peres–Schulman, *Broadcasting on Trees and the Ising Model*, author preprint](https://www.cs.ubc.ca/~will/papers/noisytrees.pdf), Theorem 1.2, gives a binary reconstruction lower bound using electrical resistance \((1-\vartheta^2)\vartheta^{-2|e|}\). Its statement was visually verified on PDF page 4 because text extraction is corrupt. This is direct precedent for a channel-variance factor. Its energy is quadratic in flow **summed over all edges**; the candidate bounds squared-flow costs along the worst ray. They are different energies, and linear reconstruction does not automatically give the four-state nonlinear converse.
- [Sly, arXiv:0811.1208v1](https://arxiv.org/abs/0811.1208v1), Theorems 1.1–1.2, treats homogeneous regular trees: q=3 for sufficiently large d, including equality, and failure of KS sharpness for q≥5. It explicitly leaves q=4 aside. [Mossel–Sly–Sohn, arXiv:2212.03362v2](https://arxiv.org/abs/2212.03362v2), Theorem 1.12, proves q=3,4 nonreconstruction at/below KS for sufficiently large-mean Galton–Watson families under Assumptions 1.10–1.11 (uniform exponential moments of offspring divided by d, and normalized offspring bounded away from zero/infinity in probability). It uses one common channel. Theorem 1.13 distinguishes four-state antiferromagnetism. Neither supplies arbitrary deterministic edge assignments or the weighted critical criterion.
- [Formentin–Külske, arXiv:0903.2962v3](https://arxiv.org/abs/0903.2962v3), Proposition 3.3, gives an exact expected symmetrized-entropy recursion; Theorem 2.1 gives nonreconstruction when expected offspring times its contraction constant c(M) is strictly below one. Extending the local identity edge by edge still gives a contraction bound, not the required q=4 capacity equivalence or its converse. [Gu–Polyanskiy, arXiv:2005.05444v2](https://arxiv.org/abs/2005.05444v2), Theorems 5–6, gives general-tree nonreconstruction under \(\operatorname{br}(T)\eta_{KL}(M^\vee,q^*)<1\), specialized to Potts. This is a strict sufficient nonreconstruction test, not an exact weighted nonlinear-capacity criterion.
- [Janson–Mossel, arXiv:math/0406447v2](https://arxiv.org/abs/math/0406447v2), Theorem 3.3 and Proposition 3.4, treat robust reconstruction for one ergodic channel below/above \(\operatorname{br}(T)|\lambda_2|^2=1\). The general-tree formulation uses antichains. Boundary-noise robustness, including erasures, does not identify a hidden-noise internal edge with a revealed erasure. Its strict spectral alternatives also leave the candidate's critical capacity question unresolved.
- The directly relevant older variable-coupling paper is [Mukhamedov–Rozikov, *The disordered phase of the inhomogeneous Potts model is extremal on the Cayley tree*, 2000](https://www.mathnet.ru/eng/tmf647). The Russian primary PDF was retrieved and pages 412, 415–417 inspected visually. Its §3 Conditions 1a/1b and 2 use \(a(x)=\sum_{y\in S(x)}[(q-1)(\vartheta_{xy}-1)/\vartheta_{xy}]^2\), requiring either a(x)≡1 or vanishing products of a along every ray, together with a uniform bound on \(b(x)=\sum_{y\in S(x)}|J'_{xy}|\). Lemmas 2–3 and the final argument prove Property E (extremality). This is a sufficient condition on a regular Cayley tree with bounded couplings, not the proposed iff for all bounded-child trees. Here \(\vartheta\) is their exponential coupling parameter, **not** the candidate's channel eigenvalue.
- The primary publisher page for [Mukhamedov–Akın, *Exact solution for the three-state asymmetric Potts model on a Cayley tree*, July 2026](https://doi.org/10.1016/j.chaos.2026.118118), describes three states, two branch-coupling constants, translation-invariant Gibbs phases and their extremality. Only the publisher's abstract/section previews were accessible and used; no numbered theorem from its unavailable full text is claimed checked. Its stated scope is distinct from four-state arbitrary-edge capacity. [Gu–Polyanskiy, arXiv:2303.14688v2](https://arxiv.org/abs/2303.14688v2), Theorem 1, concerns BP stability/boundary irrelevance on homogeneous regular or Poisson trees in specified small- or large-signal regimes. [Lee, arXiv:2609.33263v1](https://arxiv.org/abs/2609.33263v1), Introduction and main-result setup, takes q→∞ and growing observation depth with one common edge parameter. Neither boundary-noise result covers this fixed q=4 arbitrary-edge claim.
- [Ayuso Ventura–Berger, arXiv:2404.11564v2](https://arxiv.org/abs/2404.11564v2), Proposition 1.4, restates a scalar-recursion comparison; its principal conductance asymptotics concern Galton–Watson trees with \(R_v=(R_n)^{-|v|}\), where R_n is fixed within each depth-n tree. Its random-cluster application has wired boundary and cluster weight in (0,2]. Remark 1.3 explicitly warns of a conjugate-exponent convention relative to Pemantle–Peres. Merely matching the notation “p-conductance” would compare different quantities. It does not provide the missing four-state experiment comparison.

**5. Common-channel chains and degree-two subdivision: what really reduces.** The channel semigroup identity is

\[
P_aP_b=P_{ab}.
\]

Consequently a chain of k copies of one fixed \(P_c\), 0<c<1, realizes exactly \(P_{c^k}\). If every original edge has \(\lambda_e=c^{k_e}\), k_e a positive integer, subdivision gives a genuine reduction to the pinned constant-channel theorem. Writing Q for the squared-channel product at an original parent, and f for the constant flow on the replacement chain,

\[
\sum_{j=1}^{k_e}\left(\frac f{Qc^{2j}}\right)^2
=\frac{f^2}{Q^2}\frac{c^{-4k_e}-1}{1-c^4}.
\]

The proposed original-edge cost is \(f^2Q^{-2}(c^{-4k_e}-1)\). Thus the capacities have exactly proportional potentials. Unbounded but finite subdivision lengths cause no problem: each finite original truncation has finitely many replacement vertices, so the finite cutsets are cofinal. Markov screening and data processing compare these cutsets to ordinary depth levels. Subdivision preserves the child bound.

More generally, a finite series with parameters \(\lambda_1,\ldots,\lambda_k\) and product L satisfies the **exact** identity

\[
\sum_{j=1}^k\frac{1-\lambda_j^4}{Q^2(\lambda_1\cdots\lambda_j)^4}
=\frac{L^{-4}-1}{Q^2}.
\]

The proposed weight is therefore the series-invariant choice: its squared resistance is \(R_w^{-2}-R_v^{-2}\). Recognizing that telescope is routine. The whole theorem for subdivisions of a homogeneous tree, and the ray calculation itself, should not independently count as substantial findings.

The reduction does **not** realize arbitrary parameters by a single fixed c: a nonempty common-channel chain has parameter at most c and can realize only integer powers. Splitting a weak edge into equal-root factors raises those factors; this is precisely the useful Pemantle–Peres maneuver near zero. Splitting an already near-perfect edge produces still stronger factors and cannot enforce an upper bound below one.

Indeed, for any fixed \(\Lambda<1\), the pinned proof adapts routinely to arbitrary \(0<\lambda_e\le\Lambda\): replace geometric powers by channel products bounded by \(\Lambda^{j-i}\), use the smoothed local bound with \(Z\ge1-\Lambda\), and note that \(1-\Lambda^4\le1-\lambda_e^4\le1\) makes weighted and unweighted potentials comparable. A lower bound on the positive edge parameters is not needed in that adaptation. **Removing separation from zero alone is not the substantial part.**

**6. Approximation, embeddings, contractions and copy gadgets.** These deserve separate treatment because the preceding exact subclass does not exhaust conceivable reductions.

*Rounding edge lengths.* Rounding each \(-\log\lambda_e\) to a positive integer multiple of \(-\log c\) can lose a fixed factor at every generation. The accumulated error need not be bounded. Rounding cumulative root-to-vertex lengths instead can keep path products comparable, but yields zero-length edges and both signs of local channel error. Comparable root-to-leaf products do not identify the joint boundary experiments: internal shared noise affects correlations between descendants. No two-sided experiment comparison follows from that arithmetic alone.

*Moving noise to the terminals.* Consider a root passing through \(P_a\) to u, followed by two perfect copies of u. Each root-to-leaf marginal is \(P_a\), but the two leaf labels always agree. If the shared noise is replaced by two independent terminal channels \(P_a\), those same marginals remain while at a=1/2 the conditional probability that the leaves disagree is 9/16. Thus channel smoothing does not commute with branching. This explicitly defeats the proposed independent-terminal realization, not every imaginable comparison kernel.

*Perfect-edge contraction.* A finite unary perfect stretch can be removed exactly. Arbitrarily large perfect branching clusters cannot simply be contracted while invoking the bounded-child source theorem: a perfect binary cluster of height h can expose \(2^h\) exit edges at one contracted vertex, and an infinite component can leave an infinite boundary at zero noise distance. Grouping near-perfect regions until a fixed attenuation is reached encounters the same branching issue and may never reach that attenuation on a summable-noise ray. A pruning/comparison theorem that preserves positive capacity and reconstructibility could conceivably rescue such an approach; none of the inspected source statements supplies it. Proving such a theorem would itself be additional work.

*Fixed-channel branching simulation.* A finite-degree rooted gadget made only from one \(P_c\), c<1, cannot simulate channels arbitrarily close to perfect transmission uniformly over all edge parameters. Even observing the gadget's first-generation spins is an upper bound on its information. If there are at most D such spins, the event that all D channels use their independent-refresh part has probability \((1-c)^D>0\). Conditional on that event their joint law is root-independent. Subsequent observations are degraded versions. The root-conditioned distributions consequently have a common component of that fixed positive mass. They cannot reproduce the pairwise TV distances \(\lambda_e\to1\) of the desired channels. Letting D grow with e discards the fixed degree bound; increasing depth with D fixed does not remove the first-generation obstruction.

*Erasure/copy networks.* The identity \(P_\lambda=\lambda I+(1-\lambda)U\) is a hidden mixture. Revealing the copy/refresh indicator produces a different, stronger experiment: its one-edge quadratic information is 3λ, whereas the hidden Potts channel has 3λ². On the binary tree with λ=2/3, the revealed root copy cluster survives with positive probability because 2λ>1, yet the homogeneous four-state model does not reconstruct because 2λ²=8/9<1, by the accepted threshold theorem. This is an explicit failure of equivalence. Hiding the indicators restores the original hard posterior problem. Mixture closure of the upstream class and known erasure-robustness results do not justify revealing internal flags for an iff theorem.

*Finite-depth continuity.* For the candidate's ray, capping every edge at any fixed c<1 destroys reconstruction, while the uncapped ray reconstructs. Every finite-depth distribution approaches its uncapped version as c increases to one. Therefore finite-depth continuity cannot justify interchanging that approximation with the infinite-depth infimum. This rules out a particularly tempting shortcut from compact parameter ranges.

These are precise failures of the proposed standard transformations. They are not a proof that no undiscovered reduction exists.

**7. Why binary encodings and linear estimators do not close the gap.** Label four colors by two bits. Each bit separately evolves through a binary symmetric channel with bias λ, but the two edge noises are correlated: the probability both bits flip is \((1-\lambda)/4\), whereas two independent bit channels would give \((1-\lambda)^2/4\). Thus two independent applications of Ising reconstruction do not encode the four-state experiment.

There is also a concrete separation from the electrical criterion on a bounded-child tree. Let the number of depth-n vertices be

\[
N_n=2^{\lfloor n/2\rfloor+\lfloor\log_2(n+1)\rfloor}.
\]

This is realizable spherically symmetrically with each offspring count in {1,2,4}; \(N_n\asymp(\sqrt2)^n n\). Choose constant \(\lambda^2=1/\sqrt2\). The equally splitting flow has the four-state p=3 path energy comparable to \(\sum n^{-2}<\infty\), but the free-Ising electrical criterion with the same λ has resistance sum comparable to \(\sum n^{-1}=\infty\). Spherical symmetry minimizes each relevant flow criterion. Under the accepted capacity source and the classical binary criterion, the four-state process reconstructs while observing either bit alone does not. This example is already covered by the constant-channel corpus; it is used solely to invalidate a routine binary/linear reduction, not offered as another new finding.

**8. The remaining substantive step and targeted mathematical recheck.** The candidate's necessity proof is a direct weighted version of the source's \(m\mapsto m+Km^3\) and flow telescope. The unsmoothed local estimate is useful but short: feasibility gives \(|N_i|\le Z\), so the third-moment remainder stays bounded even as Z→0. This is a strengthening of the source's algebra, not an independent major innovation.

The consequential change is preserving the **branch-splitting loss** throughout the converse. For \(t_{vw}=\Theta(w)/\Theta(v)\), the deficit is zero on a unary vertex, and its propagated third-moment term carries \(t_{vw}(1-t_{vw})\). Along a flow-sampled ray put \(\alpha_i=1-t_{i+1}\). The candidate turns weighted edge energy into

\[
\mathbb E\sum_{i<n}\alpha_iX_i^2\le M^2+\varepsilon^2,
\]

and uses \(K_{ij}=\prod_{k=i+1}^j\sqrt{t_k}\), whose α-weighted row and column sums are at most two. The identity

\[
X_iX_j\prod_{k=i+1}^j\lambda_k
=X_i^{3/2}X_j^{1/2}K_{ij}
\]

and weighted Young's inequality then control accumulated loss without any uniform channel decay. This is not an invocation of the scalar-capacity recursion: it supplies the probabilistic comparison that recursion lacks. It applies with arbitrarily long nearly deterministic transmissions and arbitrarily uneven branching, not just to a subdivided homogeneous special case.

I rechecked the issues highlighted by the prior art: exact series invariance, perfect-edge degeneracy, distinguishing worst-ray from electrical energy, and the failure of compact-parameter approximation. The independent proof review's arguments at Z=0, in the conditional replacement of β by α, and at the terminal index remain adequate. The latter replacement is only inside expectation under a factor measurable through the descendant vertex; it does not assert independence of branch fractions. There is no additional proof repair requested.

The exact ray \(\lambda_j=1-(j+1)^{-2}\) has product \((n+2)/(2(n+1))\), limiting TV advantage 3/8, and unit-flow potential 15. A perfect ray has zero potential and advantage 3/4. These are diagnostic checks of the right weighting, not the significance argument.

**9. Acceptance boundaries.** The contribution merits one finding because it establishes an exact criterion beyond the range where either the fixed-channel source proof or the standard subdivision comparison works, using a complete, independently reviewed uniform estimate for the actual four-state posterior process. The appropriate description is:

> Conditional on the pinned four-state posterior-law input, a flow-splitting energy argument proves the weighted nonlinear-capacity criterion for arbitrary positive ferromagnetic edge parameters, including perfect transmission, on bounded-child trees.

Avoid claims of a new capacity theory, first recognition of the near-perfect obstruction, a new ray theorem, or automatic extensions to other alphabets or unobserved random environments. Compact-range variable channels, the source's original criterion, and consequences of the same new bridge should not increase the count separately. A materially stronger future research target would require a new probabilistic comparison, for example a sharp criterion for genuinely noncommuting/asymmetric four-state channels; that is not proved here and is not needed for this recommendation. Simply adding zero edges by pruning is not such a target.

The search is necessarily bounded. The full texts of the principal capacity, threshold, entropy, and older inhomogeneous-Potts papers were available for the relevant comparisons; the 2026 three-state publisher preview is explicitly a narrower access limitation. No matching statement was located, but that fact alone has no deductive force. The positive significance assessment comes from isolating the missing comparison and testing plausible reductions against exact identities and counterexamples.

**10. Reproducibility and artifact contract.** All artifacts are under this review path or the two assigned `i08_variable_capacity_novelty_r3` directories. The [artifact manifest](../sources/i08_variable_capacity_novelty_r3/artifact-manifest.json) hashes the report, source snapshots, all 41 pinned raw source files, primary PDFs, extracted text, inspected page renders, saved web results, and scripts/results, excluding its own self-hash. The final verification also checks the original candidate and proof-review hashes have not changed. The parent-owned `TEN-FINDINGS.md` changed during the audit; its initial hash is preserved in the input manifest, and its observed final bytes and hash are retained as contextual evidence. The count remained two. This reviewer did not edit that index or audit the later extension mentioned there.

Run from the repository root:

```bash
python frontier/experiments/i08_variable_capacity_novelty_r3/check.py
python frontier/experiments/i08_variable_capacity_novelty_r3/verify.py
```

The independent exact-arithmetic checks cover 16 channel-composition pairs, 120 common-channel subdivision identities, three general series telescopes, 100 exact ray prefixes, the shared-versus-terminal noise discrepancy, observed-copy and two-bit obstructions, and three 40-step splitting-kernel paths with perfect, weak, near-perfect and almost-unary transitions. They pass. These are finite tests supporting the reduction audit, not proofs of the infinite theorem. `retrieve.py` reproduces pinned source retrieval and inventory screening; `retrieve_literature.py` reproduces successful primary-file retrievals and checks their recorded hashes in memory. The search ledger records scope and access limitations. No other finding or shared index has been changed by this audit.
