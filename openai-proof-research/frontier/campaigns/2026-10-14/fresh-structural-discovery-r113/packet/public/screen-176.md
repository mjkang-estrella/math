# 176 — the compatible rainbow lift is already paid

This is a pre-freeze calculation, not a frozen candidate or substantiality decision. Write q=p_E(n,H), h=e(H)≥1, and take c≥h colors. All copies below are ordinary, not induced. Isolated vertices can be restored exactly as in the source. The proposed direction was an absolute-constant rainbow appearance bound on the scale q(1+log₂h), including exactly h colors.

## Strongest source contract

The sole catalogue manuscript, *The second Kahn–Kalai conjecture*, supplies `lem:hierarchy` in `sections/graphs.tex`: nested H_0=∅,…,H_k=H with |H_(i−1)|<|H_i|/17, a tree of all extension histories, conditional spread σ=128q, and capacities ℓ_i=|H_i|−|H_(i−1)| satisfying ℓ_(i+1)≥16ℓ_i. Its `thm:tree` in `sections/trees.tex` accepts any finite ground set and any such disjoint probability tree. It covers a path with probability at least 2/3 at density 16 exp(50)σ(1+log₂ℓ_k), when that density is at most one. The resampling, outside-target distortion, simultaneous descendant potential, and retained-tree recovery are paid operative contracts, not proposed new deductions.

The hierarchy does not assert σ-spread of the complete-path law. Applying a global rainbow-spread theorem directly to that law would therefore skip a hypothesis.

## Exact compatible reduction

Lift the ground set to E(K_n)×[c]. Each tree node remembers its original history and an injective coloring of its current edge set. At a child first choose the original extension according to its source law, then choose uniformly an injection from its added edges into the colors unused by the parent. Keep all distinct histories. Path labels remain disjoint, their uncolored projections are the original copies, and all colors along a path are distinct.

At level i the parent has s=|H_(i−1)|<h/17≤c/17 edges. There are a=c−s≥16c/17 available colors. For a prescribed set J of r colored pairs, incompatible repeated edges/colors have probability zero. Otherwise the chance its uncolored projection lies in the extension is at most σ^r, and, conditional on this event, its specified color assignment has probability 1/(a)_r. For 1≤r≤a,

    (a)_r ≥ (a/e)^r.

Indeed the average of the largest r numbers among log(1),…,log(a) is at least the average of all of them, and log(a!)≥a log a−a by integration. Thus every lifted child law is σ'-spread with

    σ' = 17eσ/(16c).

Capacities are unchanged. Apply the *same source tree theorem* on the lifted ground set. Put

    p = 2176 exp(51) q (1+log₂h).

If p≤1, independent selection of each colored pair at density p/c contains a rainbow copy with probability ≥2/3. (The actual source-required density can be smaller because ℓ_k≤h.)

Now replace the independent colored-pair experiment, one original edge at a time, by an edge present with probability p and carrying one uniform color. Given all other edges, either a witness is already present, no color can complete a witness, or precisely a set D of colors can complete one. In the third case the old conditional success probability is 1−(1−p/c)^|D|; the new one is p|D|/c, which is at least as large by the union bound. Every witness uses at most one color on each original edge. Sequential replacement proves the asserted ≥2/3 probability in the single-color random graph model. Monotonicity permits every larger admissible edge probability as well.

This is a complete compatible reduction in its stated nonvacuous regime. It is not a claim with p replaced by min{1,p}: for H=K_n there is only one possible complete edge set, and with c=h the probability that it is rainbow at p=1 is h!/h^h, below 1/2 for large h. This was checked during feasibility, before any freeze.

## Primary operation comparison

Han–Yuan, *On Rainbow Thresholds*, [arXiv:2310.03974v2](https://arxiv.org/pdf/2310.03974v2), §2 proof of Theorem 8, constructs the colored-pair ground set and proves the same falling-factorial spread estimate (equation (3)). §3 Lemma 12 proves exactly the independent-colored-pairs to single-color coupling used above. Their global spread hypothesis is not silently substituted for the source tree. Instead, their injective-color calculation is applied separately at every already supplied source node; the source's 17-fold predecessor reduction provides the uniform color reserve. This explicit compatibility check pays the integration: no new descendant potential, resampling lemma, color-collision correction or simultaneous embedding operation remains.

The source explicitly credits Tran's core extraction and the existing planted-posterior resampling architecture. Their full primary bodies were not newly read here; no independent claim about their complete scope is made. Han–Yuan's proofs, rather than its abstract, establish the color operations used in this screen. Ferber–Krivelevich was retrieved as a precursor but not semantically read and is not an additional proof premise.

No nominee. The distinction from a global-spread black box does not, after the stronger source contract is checked, leave an unpaid operation.
