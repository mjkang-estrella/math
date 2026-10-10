# I36 common geometric avoidance: independent significance / prior-art review R3

**Recommendation: TECHNICAL ONLY. Original-proof disposition: retain R2 PASS WITHOUT REPAIRS.** Theorem A is a real strengthening of the statements in the primary sources compared here. I did not find an exact prior statement with its common-set quantifiers, and I do not classify it as DUPLICATE. Under this project's stricter operation-based substantial-finding gate, however, its remaining step is a technical combination of the stipulated routing construction with already-used physical clipping and finite-dimensional grid-signature partitions. The reduction below identifies the obligations and pays them explicitly; the verdict is not based merely on the words “standard arrangement,” or on failure to find an exact theorem.

This review changes no accepted count. If the parent records A, record one technical consequence, with infinite omission as its tail corollary. The Hilbert-valued transfer, variation obstruction and unresolved supergeometric candidate do not add findings. No upstream truth audit was performed.

## 1. Exact result, scope and retained proof judgment

For every `0<η<1`, A constructs one compact `Eη⊂[0,1]` with

`m(Eη)≥1−7η/16>1−η`,

such that for every `q∈(0,1)`, `x∈R` and nonzero signed `s∈R`, there exists `n≥1` with `x+s q^n∉Eη`. The set is independent of q. Replacing s by `s q^N` shows infinitely many omitted terms for each triple; this is the same result. There is no uniform first-hit index, no claim to avoid all finite prefixes, and no claim for independently varying adjacent ratios.

I read the full author report and R2 proof review, the complete geometric and dyadic companion proofs (G and D), and the primary passages specified below. I independently checked the compatibility of the proposed common windows, the conditional-routing interface, the local parameter count and the order of parameter choice. I found no new mathematical gap or counterexample. In particular, the eventual open-neighborhood repair is performed after the supremum over the compact parameter rectangle, and may hit a term beyond J. It does not weaken the assertion to almost every center or parameter.

The author report remains SHA-256 `acc4b9f04d9f90c6dfa4cb54333c2c57026a87d8fc4030ce8f832405b943eb5f`; R2 remains `1f8f1c37a3c716d0a7f4e4f0700a15f92bf66cb6019ac774be48403a7c81246c`. There is no repaired statement in this review. The **significance** judgment below is separate from those proof conclusions.

## 2. Primary comparison: statements and limiting quantifiers

All OpenAI dependencies are accepted at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. G is *The geometric case of the Erdős similarity conjecture*, October 5 manuscript, especially `03-windows.tex`, `04-routing.tex`, `05-scales.tex`; D is the September 25 dyadic companion, all proof sections. The [pinned manifest](../sources/i36_common_geometric_avoidance_novelty_r3/pinned-manifest.json) gives all 23 G/D text-artifact paths, SHA-256, Git blobs and immutable raw URLs. These two are the direct similarity companions found by the complete inventory screen.

| Primary result / proof | What it provides | What it does not already state |
|---|---|---|
| G, main theorem and complete window/routing/scale proof | For each fixed q, a compact arbitrarily large-measure set avoiding every affine copy of that geometric sequence, either sign; local routing amplification and center repair | One E for uncountably many q. G's grids and fixed index windows depend on q |
| D, complete proof | Dyadic version and underlying padded-tree/local-subtree construction | General-q simultaneity; its dyadic index shift cannot be used for arbitrary q |
| [Jiang–Xi, 2610.11449v1](https://arxiv.org/abs/2610.11449v1), complete proof, particularly Lemma 2.1, Lemma 5.1 and Corollary 6.1 | A prescribed positive null sequence with liminf adjacent ratio positive, and a prescribed **countable** family, can be avoided; bounded-ratio subsequence, sequence-dependent grids, one dilation parameter | A single set for all geometric ratios, or all bounded-variable-ratio sequences. Corollary 6.1 uses summable countable unions |
| [Burgin–Goldberg–Keleti–MacMahon–Wang, 2210.09284v1](https://arxiv.org/abs/2210.09284v1), Question 1, Theorem 1.1, Proposition 3.3, with proofs | Theorem 1.1 excludes all zero-centered `a q^n` while retaining a density point at zero. Proposition 3.3 excludes almost every parameter triple | Theorem 1.1 does not exclude every translated sequence; Proposition 3.3's Fubini argument does not control projection of all bad triples onto centers |
| [Chlebík, 1512.05607v1](https://arxiv.org/abs/1512.05607v1), parameter-plane covering and Theorem 15 proof | Relative-gap hypotheses permit finite representative counts and small exceptional-center repair | Its relative-gap criterion is not a geometric-sequence theorem: geometric finite subsets have exponentially small normalized minimum gaps |
| [Kolountzakis 1997, correct author PDF](https://eigen-space.org/mk/ps/universal.pdf), independently visually read pp. 3–11 | Random cells, finite representatives, a.e. affine copies; Theorem 2 controls bad projection onto the **scale axis**; §2.2 explains why a small **center-axis** projection would allow repair; Theorem 3 uses a relative-gap condition | All centers and all scales for geometric sequences. Projection onto the wrong axis cannot substitute for the required estimate |
| [Kolountzakis–Papageorgiou, published 2025](https://msp.org/apde/2025/18-1/apde-v18-n1-p02-p.pdf), complete relevant §§3–4 | §3 clips a moving transformed sequence to a physical interval. Remark 3.2 isolates separation, sufficiently many trials, and bounded event complexity. §4 partitions a finite-dimensional map space by cell-crossing hyperplanes, selecting representatives before the random test | Its separation/count assumptions do not directly cover null geometric sequences; the routing amplifier must come from G/D |

The last comparison is decisive at the level of method, rather than theorem implication. In KP §3.1, the tested index set `M_N(x,t)` changes as points enter or leave `[-N,N]`; it is not a fixed-index argument. In §4, the crossing equations are linear in transformation coordinates and give polynomially many regions with constant cell signature. I36 supplies the explicit logarithmic coordinates in which its own crossing equations have that form. Thus both moving membership and more than one continuous parameter have prior operational implementations. This is more specific prior art than citing only KP's one-dimensional dilation representatives.

For completeness, the older criteria really do miss the hard input. For an m-point subsequence of `{q^n}`, its minimum gap divided by its diameter is at most `q^(m−2)/(1−q)`: use the last gap for the numerator and the first point times `1−q` for a lower bound on the diameter. Hence `−log δ` cannot be `o(m)`, as in the relevant relative-gap argument. Likewise, in a bounded normalized geometric copy, the number of points separated by `N^(−β)` is only `O_q(log N)`. KP Theorem 4.1's required `α(N)/log N→∞` is unavailable. **I am not claiming that any of these old theorems, used as a black box, proves A.** The exponential-trial amplifier that overcomes that obstacle is precisely an accepted G/D operation.

## 3. Operation-by-operation account

Here “additional” means additional to the fixed-sequence G/D proof, not automatically substantial or absent from all other literature.

| Operation already supplied | Exact additional obligation | I36 solution | Closest prior proof / assessment |
|---|---|---|---|
| Finite ordered M-ary tree; independent selector and terminal tables; mean density p | Use one random object for all q in a slab | q-independent dyadic grids and common physical windows | G/D routing architecture unchanged |
| Padded edge-plus-child blocks of relative span at most twice the window size | Retain enough active sequence terms when indices vary | Count integers in a logarithmic interval of length `r log2/log(1/q)` | KP §3 physical clipping; elementary arithmetic-mesh count verifies its trial-count condition |
| Source separation needed for fresh table entries | One grid must separate every fixed-parameter active set uniformly over the slab | `2^(−ℓ)≤(1−q_+)/4` and grid width `2^(−b−ℓ)` | G separation lemma with uniform physical lower gap substituted; no simultaneous independence across different parameters is asserted |
| Earlier-key stability and small unstable-center set | Stability must hold for every permitted displacement, not a representative q | Exclude all earlier grid boundaries within `2^(−a)`; cost `K 2^(ℓ−g)` | Same G/D geometric key-stability argument, now stated for an interval of displacements |
| Full center-selector exposure; first default | Avoid accidentally exposing trial addresses as active indices change | Fix parameters after center exposure; all active current addresses distinct from the center address | G/D conditional-entry invariant unchanged |
| Terminal product bound after all selectors are fixed | Adaptive routes may share leaves | Distinct full `(leaf,key)` addresses by nested grids; separate child tables | G/D conditional-terminal argument unchanged |
| Local success implies global hit | Do not count unrelated later/finer subtrees | Use only one edge and its child block | G/D local-subtree implication unchanged; essential to entropy budget |
| Finite dilation representatives | Include moving-index membership and q variation | Entry/exit lines plus cell-crossing lines in `(v,u)=(log t,−log q)` | KP §3 moving membership plus §4 finite-dimensional signature partition |
| Polynomial arrangement count | Half-open cells, rectangle sides and equalities cannot be discarded | Include all 0-, 1-, 2-dimensional strata, with duplicate/concurrent lines harmless | Standard full-stratification refinement of the same signature method; R2 checks its actual implementation |
| Branching beats an exponential local representative cost | Two parameter dimensions double the relevant exponent | Choose `β=p(M−1)κ/2>4log2+1` before tree depth and final window size | Same G/D “choose branching first” amplification, changed coefficient |
| Finite padded recursion | J grows with the final window size | Prove `J≤C_J(r0+g+1)`; retain its square until choosing r0 | Finite affine recursion, detailed below; not an unproved uniform constant |
| Mean-density selection and exceptional-center repair | Take the supremum over the full parameter rectangle before repair | Open enlargement and compact projection; then open cover of bad centers | G/D center repair with a compact two-dimensional parameter set; topology unchanged |
| Countable scale assembly and reflection | Cover q→0, q→1 and all signed scales | Countably many already-uniform slabs and signed dyadics with summable budgets | Existing summable assembly; no uncountable intersection or general-q dyadic index shift |

### A reduction certificate for the allegedly new bridge

Fix `p>0`, `0<q_-≤q_+<1`, and `1≤t≤2`. Write `Lmin=log(1/q_+)`, `Lmax=log(1/q_-)`, `κ=log2/(2Lmax)`. The source routing proof only needs a supply of separated trials in each local block, stability of earlier addresses, and a deterministic bound on how many local truth signatures vary with the parameters. It does not use the names or fixedness of the integer indices after these properties have been established.

Take the same padded tree in logarithmic physical coordinates. In an edge `[a,b]`, set `I(t,q)={n≥1:a log2≤nu−v≤b log2}`. If `r=b−a≥2Lmax/log2`, then `|I|≥r log2/Lmax−1≥κr`. This proves the required trial-count input, including membership changes. A fixed-reference-q grid would fail, but replacing it by `N_b=2^(b+ℓ)` gives separation at least `(1−q_+)2^(−b)` and a nested grid independent of q. Prior-key stability follows from the same physical upper displacement bound. These verifications alter constants and indexing; they do not alter the conditional probability invariant of the source.

For a local edge-plus-child block let `b*−a≤2r`. Its finest grid has at most `1+2^(ℓ+2r)` relevant boundary offsets in the physical window, up to the harmless endpoint allowances used in I36. All membership and key changes are therefore among

`v−nu=−a log2`, `v−nu=−b log2`, `v−nu=log(γ−x)`

for the relevant positive offsets `γ−x` and `n≤J`. These are affine hyperplanes in two real variables—the exact finite-signature operation used in KP §4, after a different explicit coordinate map. Including rectangle boundaries and all strata gives I36's bound

`8[5+(M−1)J(3+2^(ℓ+2r))]^2`.

The representatives depend on x and the exposed first-default location, but not on unexposed table values. Constancy of active membership and finest keys fixes every local test. This verifies the interface to the fixed-parameter source bound `exp(−βr)`. No independence between representatives is needed for a union bound. No common trial-index set is needed between different representatives.

The subtle possible circularity can be eliminated even more explicitly than the author's bound. For `M≥2`, `r0,g≥1`, put

`P_h=M(2M)^(h−1)`,

`Q_h=(M−1)(2M)^(h−1)+(3M−1)((2M)^(h−1)−1)/(2M−1)`.

The same source-style padding recurrence in I36 gives **exactly** `σ_h=P_h r0+Q_h g`. Indeed `σ_1=M r0+(M−1)g`, and for every `h≥2`, `g+σ_(h−1)>r0`; hence `r_h=g+σ_(h−1)` and `σ_h=2M σ_(h−1)+(3M−1)g`. The displayed formula follows by induction. Thus after M and d are fixed, `B=3+σ_d` and `J=ceil((B+1)log2/Lmin)` grow only linearly in r0 and g. Large coefficients depending on the fixed depth do not create an exponential in r0.

Multiplying the signature count by the source failure estimate gives

`C0(r0+g+1)^2 exp[−(β−4log2)r]`,

where `C0=648 M² 2^(2ℓ) C_J²` can be fixed before r0 using the author's stated `C_J`. Choose ℓ, then M with `β>4log2+1`, then d to make the no-default probability less than p, then g to control unstable centers, then r0. Since `r≥r0`, the last displayed expression tends to zero. This is the same exponent-versus-branching operation as G's one-parameter representative estimate. Increasing parameter dimension changes the entropy coefficient that M must dominate; it does not require a new amplification principle.

Finally, the source's finite probability space and mean-density identity apply to this common random object. Open enlargement permits compact projection over `[1,2]×[q_-,q_+]`; the repaired periodic hitting set has density at most `6p`. Countable slab and signed-scale assembly yields exactly

`12(η/64) (Σ_(j≥3)2^(−(j−2))) (Σ_(k∈Z)4^(−|k|)max(1,2^k))`

`= (12η/64)(1)(1/3+1+1)=7η/16`.

This supplies all of the claimed additional obligations while retaining the source routing law and repair scheme. It is a genuine common-set construction, not an invalid exchange of existence quantifiers. The reason to classify it as technical is that the required extension is exhausted by these substitutions into already-explicit operations, including the previously published moving-membership and multivariable partition operations.

## 4. Significance judgment against the project gate

The strongest case for SUBSTANTIAL is clear: A reverses a named existential question, has a single large compact set for a continuum of ratios, and its proof cannot be obtained by simply intersecting the fixed-q conclusions. R2 also correctly treats the moving-index and noncircular-budget checks as necessary mathematics. None of that is being denied.

The decisive contrary evidence is **positive prior-method coverage**, not a search-absence argument. G already supplies the difficult small-density hitting amplifier at logarithmically many separated points, as well as localization to each child subtree. KP explicitly permits moving membership in a physical region, isolates the separation/count/complexity interface, and implements its finite-dimensional version with crossing hyperplanes. The physical/logarithmic mesh conversion above verifies that interface using elementary estimates and the unchanged G recursion. There is no additional stochastic invariant, new entropy gain, or new repair principle left unpaid by those accepted operations.

This places A on the technical side of the project's established comparisons:

- **I14 spectral width:** an unstated global consequence survived proof review, but its work was already paid by the precise local stability inequality and the existing smoothing/transfer proof. A distinct theorem statement was insufficient.
- **I15 odd-order topology:** checking finite recursive marked-annulus assembly did not create a new invariant beyond the source operation.
- **I17 six-point Ramsey:** the adjugate/product identity in the source already paid the decisive operation, despite a new-looking finite configuration conclusion.
- **I30 Einstein stability:** exact volume-square-root control plus the established packing input was a technical substitution; proof PASS did not establish substantiality.
- **R011 rooted matching entropy:** by contrast, the additive rooted allowance `W_v=B−b_v` paid the separator charge and the positive-global-maximum deficit together. The old unrooted induction did not pay those terms, and merely introducing a rooted trace left the old threshold intact. Its new invariant removed a specific obstruction that survived the prior operations.

In A, the corresponding obstruction—an extra continuum of grid signatures—is precisely what the prior finite-dimensional representative method handles. The source's freely choosable branching pays the enlarged exponential coefficient. The fixed-depth affine calculation closes a parameter-accounting requirement rather than introducing an analogue of R011's new additive allowance. Calling all of this “automatic” without the certificate would be too loose; after the certificate, the reduction is sufficiently explicit for **TECHNICAL ONLY** under this gate.

This is a judgment about the contribution **conditional on the stipulated OpenAI operations**, not a claim that proving A without G/D would be easy or that its unconditional publication importance is settled. No exhaustive worldwide-priority claim follows from this bounded review.

## 5. Question 1, noncontradictions and failed shortcuts

A gives a negative answer to Burgin et al. Question 1 under the stipulated premises: taking any η gives a positive-measure set containing no nonconstant sequence `a q^n+b` for any q in `(0,1)`. Theorem 1.1 of that paper only fixes b=0, and its log transform does not linearize arbitrary translation. Proposition 3.3 averages over q; replacing its almost-everywhere statement by a supremum would be invalid. These distinctions are preserved.

The same paper's positive containment statements impose extra conditions. Proposition 3.1 uses a summability condition on density deficits, and the later gap/structured-Cantor results impose quantitative summability of removed intervals. A generic density point, or positive measure alone, does not satisfy those stronger conditions. Theorem A therefore does not contradict those results. Full Hausdorff dimension without positive Lebesgue measure, Rajchman hypotheses involving non-atomic measures, and avoidance of a larger twofold-sumset pattern are not the same conclusion as A and were not treated as exact competitors.

Three tempting shortcuts remain invalid:

1. Dense countable q coverage, or uniform constants in fixed-q theorems, does not give a common set. An open dense set of successful parameters need not be the whole parameter space. Even a compactness subcover argument with individual open hitting sets would need control of its covering number times its density budget; no such bound comes for free.
2. Replacing q by arbitrary sequences whose adjacent ratios stay in `[1/3,2/3]` is false. At a density point x of any positive-measure E, choose points in sufficiently small intervals `x+[0.9·2^(−k),1.1·2^(−k)]`. Their adjacent displacement ratios lie in `[9/22,11/18]⊂[1/3,2/3]`, and every chosen point lies in E. This infinite-dimensional family has no uniform finite-dimensional signature bound of the kind used above.
3. Counting every grid boundary in the globally finest tree lattice would spoil the local entropy estimate. The success implication uses only the edge and its child subtree. That localization is essential, but it is already part of G/D; I36 correctly preserves it.

The original I02 false sunflower/spread and avoiding-set convexity inferences remain rejected. The Kakeya observation there only recovers dimension four, and its rank-one perturbation result remains technical. None is revived or used here.

## 6. Evidence, current versions and reproducibility

The exact task brief, including the original research brief, accumulated objections and R2/parent results, is frozen in [full-brief.txt](../sources/i36_common_geometric_avoidance_novelty_r3/full-brief.txt). Initial immutable files and mutable ledgers were copied into the owned frozen directory. The [input manifest](../sources/i36_common_geometric_avoidance_novelty_r3/input-manifest.json) additionally binds all unchanged author/R2 artifacts and the necessary gate comparisons by hash. Actual read ranges, opening passages, hashes, immutable Git identities and primary URLs are in [read-passages.json](../sources/i36_common_geometric_avoidance_novelty_r3/read-passages.json), [read-scope.json](../sources/i36_common_geometric_avoidance_novelty_r3/read-scope.json) and the pinned manifest. These records distinguish whole-proof reads from selected sections and visual pages.

Fresh HTTP responses retained on October 9, 2026 show Jiang–Xi still at v1, submitted October 8; Burgin et al. and Chlebík still at v1; KP's arXiv current version v2, October 6, 2023, with the published 2025 proof used here. The survey current version is v2, January 1, 2025; it was only an orientation/version check. The 2020 claim is explicitly withdrawn in its current v2 record and is excluded. Version histories and all 11 successful direct responses, including headers and payload hashes, are retained. The five freshly downloaded primary PDFs are byte-identical to the retained copies used for reading. The correct 1997 PDF was independently visually read on pages 3–11 because extraction is garbled. The historical wrong guessed arXiv identifier returned Temme and is not a dependency; the old nonexistent-version and parsing failures remain in the bound author evidence. No fresh HTTP retrieval failed.

Four bounded web query/response snapshots are retained. Search results include irrelevant hits, which were not used as mathematical evidence; an earlier unretained exploratory batch is not presented as sealed evidence. The search is not a worldwide priority certificate. The strongest exact theorem comparisons are based on the primary proof texts, not snippets or survey summaries.

Unlike the prior verifier's recorded-cache-count check, this review independently read and SHA-256/Git-blob checked **all 9,340 cached text files, 141,349,121 bytes**, against the complete nontruncated 13,223-entry tree, covering **749 manuscripts**. The 719-entry catalogue lags. The full inventory, search patterns and matching contexts are retained in [corpus-screen.json](../sources/i36_common_geometric_avoidance_novelty_r3/corpus-screen.json). This was a complete text search, not semantic reading of all manuscripts. Similarity-specific matches identify G/D; other primary-name matches concern Hadamard/Fourier methods or lattice tilings and do not supply competing similarity proofs. The broad common/geometric search is deliberately noisy and is not represented as a precise semantic classifier.

Both unchanged earlier verifiers reproduced successfully. [reproduce_prior.py](../experiments/i36_common_geometric_avoidance_novelty_r3/reproduce_prior.py) runs the original R2 file with its original `__file__`, intercepting its sole report write; R2 in turn intercepts the author's sole report write. All **151 monitored author/R2 files** remained byte-identical. R2 reproduces its 23-file seal, 134 inputs, 24 pinned files, 26 passages and 18 contracts, with its exact arrangement, conditioning, tree and budget diagnostics. The author reproduction retains its 124-file seal, 39 pins, 21 contracts, 32 passages and 19 responses. No prior seal was regenerated. Historical author ledger drift and subsequent R2 ledger drift are reported separately from immutable inputs; neither is a mathematical source change.

The new small diagnostic checks only the reduction's arithmetic-mesh count and exact affine span formula: 240 rational mesh cases and 567 recurrence cases. It does not purport to decide novelty or certify the universal proof. R2's stronger partition/conditioning diagnostics are reused through unchanged execution rather than cosmetically duplicated.

Run from the repository root:

```sh
python -B frontier/experiments/i36_common_geometric_avoidance_novelty_r3/verify.py
```

The verifier checks the owned seal without regenerating it, bound immutable inputs, frozen mutable snapshots, pinned Git blobs, read-passage hashes, primary-response equivalence, all-cache search reproduction and the exact reduction diagnostic; it re-executes both unchanged prior verifiers with writes captured. It reports current shared-ledger drift separately. Its generated output is confined to this review's experiment directory. No agents, shared edits, staging, commits, pushes or publication were performed.

**Final disposition: proof PASS retained; TECHNICAL ONLY recommended; no accepted-finding increment.**
