# H036 independent GPT6Sol proposals

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h036-independent-searchgeometry-sol-20261008-r1`

Completed, no pending children. Initial proposal task was independent of other live proposals. No primary sources directly read; no novelty claims accepted. Raw report follows.

I found **three paper hypotheses worth screening**, with no verified improvement. Each is a full-range, single-target solver proposal: it would stop on a recoverable relation, verify \([k]G=Q\), and use a paid, independently blinded complete fallback after a fixed cap. The working comparison is competent signed BSGS at the same memory budget, including the roughly \(0.943\sqrt q\) proved key-count reference and the reported roughly \(0.9\sqrt q\) progression results. A favorable key count alone would not beat either solver’s complete work.

### 1. Coefficient-colored dense pair graph

**Operation.** Prepare independently labeled points \(P_i=a_iG+b_iQ\). For each directed pair \(i<j\), emit exact keys \(x(P_i\pm cP_j)\) for a small fixed set such as \(c\in\{1,2\}\), retaining the pair, coefficient and sign. An equal \(x\) key gives one of two signed linear equations in \(k\); discard zero-coefficient equations and verify the recovered scalar.

**Possible gain.** Different coefficients might prevent alternative pairings of four seeds from producing the same equation. If so, a dense graph with \(O(q^{1/4})\) seeds might approach the ideal \(0.886\sqrt q\) birthday key count without H034’s sparse-graph seed count. That leaves only a small margin against the reported progression comparator.

**Full cost and uncertainty.** Pay for seed scalar multiplications, the \(cP_j\) points, two sided additions and batched inversions, key hashing and descriptors, exact lookup, exceptions, failed relations, verification, peak records, cap waste and fallback. The unproved premise is that coefficient colors remove enough *distinct-equation multiplicity* throughout the stopped prefix. This changes H034’s C4 restriction; it is not a new paired-addition kernel. **Cheapest falsifier:** enumerate normalized four-seed coefficient vectors for every pair of colored edges symbolically, derive the prefix event count, then insert that count into the stopped-cost ledger before running any curve code.

### 2. Cached-pair, three-seed hyperedges

**Operation.** Cache \(U_{ij}=P_i+P_j\) for the pairs a frozen hypergraph uses. For each hyperedge \((i,j,k)\), emit \(x(U_{ij}+P_k)\) and \(x(U_{ij}-P_k)\). A signed key equality yields a labeled equation involving up to six seeds. Use exact descriptors and the same recovery, verification, cap and fallback rule.

**Possible gain.** A hypergraph with about \(\sqrt q\) emitted keys, few repeated six-seed equations and substantially fewer than \(q^{1/3}\) independently prepared seeds could reduce setup while retaining an ideal birthday stopping law. The pair cache and its construction must stay subleading, and any claimed key-count advantage still has to beat signed BSGS.

**Full cost and uncertainty.** Charge every seed and cached-pair addition, up to \(O(n^2)\) cached points if no smaller construction is given, the two outputs per hyperedge, batching, descriptors, lookup, peak storage, null equations and fallback. The central unsupported assumption is combinatorial: sufficiently many hyperedges may force repeated equations or an expensive pair cache. **Cheapest falsifier:** prove an extremal bound for hyperedge-pair equation multiplicity and required pair support, or supply an explicit family and count both exactly. No synthetic ECDLP run is useful before that count.

### 3. Short-jump seed factory for the H034 solver

**Operation.** Prepare a small table of independently labeled jump points \(J_r=\alpha_rG+\beta_rQ\). Generate H034’s source points through a frozen, nonbacktracking sequence \(P_{i+1}=P_i+J_{\sigma_i}\), carrying their known affine labels. Feed them into the existing sparse paired-sum graph, then use its exact collision recovery and complete fallback.

**Possible gain.** Generating \(n\) source points by paid additions could replace \(n\) separate scalar-multiplication preparations. This targets **finite complete work**, not the square-root exponent or H034’s leading key cost. The H034 capped diagnostic spent heavily on setup, but its seven completed sampled cases still lost to the primary comparator and reached no candidate leaf search.

**Full cost and uncertainty.** Pay for jump-table construction, every walk addition, source storage, graph/key generation, lookup, failures, cap and fallback. These sources are correlated: H034’s independent-label collision law cannot simply be reused. **Cheapest falsifier:** for a frozen jump sequence, express every prospective collision as a linear form in the independent jump labels; count proportional forms and low-rank clusters. Reject the proposal if those dependencies consume the saved setup or invalidate the needed stopped-hit law. Compare the resulting complete ledger with an equally optimized baseline.

I read the project rules, checkpoint and H019–H034 dispositions, including the [H034 graph barrier](/home/mj-kang/Documents/Dev/math/dlp-research/research/findings/H034-balanced-graph-barrier.md), [H034 capped result](/home/mj-kang/Documents/Dev/math/dlp-research/research/findings/H034-initial-diagnostic-result.md) and [H019 full-work screen](/home/mj-kang/Documents/Dev/math/dlp-research/research/findings/H019-fullwork-disposition.md). I did **not** directly read the primary papers those records cite, so these are prior-art distinctions relative to the project record, not novelty claims. I did not read H035 independent-information proposals or live H036 proposals, edit files, execute code or run experiments.
