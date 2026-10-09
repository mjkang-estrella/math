# H036 dense-triple independent Opus review

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h036-hyperedge-count-review-opus-20261008-r1`

Completed with no pending children. Raw testimony retained; root qualifications
are separate. Unverified source memories, cost estimates and provider usage
figures are not accepted as calibrated research evidence.

I've finished checking the argument. **Verdict: it is valid as a scoped key-count falsifier of the dense complete-triple construction, once three hypotheses are made explicit.** I found no counterexample and no constant error. I didn't run, import or edit anything, and spawned no children. I read the Sol card (`H036-searchgeometry-sol-raw.md`), `H034-balanced-graph-barrier.md`, and the 0.943 and 0.90 references in `H025-scaling-reconciliation.md` and `H024-manygiant-priorart-raw.md`.

## Accepted statement

**Hypotheses:**
- q is an odd prime.
- Sources are P_i = a_iG + b_iQ with (a_i, b_i) independent and uniform in F_q². The target scalar k is fixed and arbitrary.
- The solver emits x(P_i+P_j+P_k) and x(P_i+P_j−P_k) for all i<j<k. Triples are ordered by nondecreasing newest vertex k, in any order within a layer, and both outputs of each triple are emitted.
- **(H1)** Enough keys exist: 2·C(n,3) ≥ √(q/0.4) ≈ 1.581√q.
- **(H2)** A success needs a key hit, a direct exceptional recovery (a source, cache or output being O, an equal-input addition, Q=O), or the paid fallback.

**Conclusion:**

E[min(T, 3√q)] ≥ (2/3)·√(q/0.4) − O(q^{1/3}) ≈ 1.054√q − o(√q).

Here T is the number of keys inspected up to and including the first successful recovery. All seed setup, pair cache, exceptions and fallback only add to this. The bound holds for every fixed k, so it also holds averaged over k.

**What it falsifies:** it rules out a key-count win for this construction against the proved 0.943√q two-family comparator, by a factor ≥ 1.118. It also falls below the ideal 0.886√q and the experimental 0.90√q, so it loses to those too.

**(H3) Turning this into a complete-work statement needs one more condition.** The per-key price of a paired x(U_ij ± P_k) output must be at least 0.895 (0.943/1.054) times the comparator's per-key price. It is the same shared-inversion paired-addition kernel (about 2.5M+S per key), so this is plausible, but the proof doesn't establish it. State it as an assumption.

## Constant and logic checks

| Item | Check |
|---|---|
| No structural zeros | A formal combination e_i+e_j+s·e_k with i<j<k determines its triple and sign uniquely. So two distinct outputs are never formally equal. A = −B is impossible because A has at least two +1 coefficients and −B has at least two −1 coefficients. Every collision form A ∓ B is a nonzero vector. |
| Same-triple outputs | x(U+P_k) = x(U−P_k) gives the forms 2e_k and 2(e_i+e_j). Both are nonzero; they vanish only on P_k=O or U_ij=O. These are counted among the O(n⁵) forms. |
| Probability 1/q | Each coefficient satisfies \|c_v\| ≤ 2 < q. The a_v terms alone make Σc_v(a_v + k·b_v) uniform, so the probability is exactly 1/q for any fixed k, including k=0. |
| Six-support count | The vectors are ±1 on six vertices, up to sign: at most 2⁵ = 32 per 6-set. 32·C(n,6) ≈ (2/45)n⁶ and t² ≈ n⁶/9, so the ratio is 0.4. ✓ Consistency: there are 80·C(n,6) form incidences, so each distinct form has multiplicity at least 2.5. This is just an upper bound; whether all 32 patterns occur doesn't matter. |
| Exact prefix bound | 20·C(m,6) = C(m,3)·C(m−3,3), so 32·C(m,6) = 1.6·C(m,3)·C(m−3,3) ≤ 0.4·(2C(m,3))² ≤ 0.4t² whenever layers 1..m are complete. The partial layer m+1 only adds 32·C(m,5) = O(m⁵) = O(t^{5/3}). |
| Shared-vertex forms | The support is at most 5 and coefficients lie in {−2,…,2}. That gives at most Σ_{s≤5} C(m+1,s)·4^s = O(t^{5/3}) forms. ✓ |
| Exceptions and direct recovery | The extra forms are output = O (t forms), U_ij = O and P_i = ±P_j (O(n²)), source = O (n), and Q = O (one event, O(1/q)). That totals O(t) forms. If the cache entries are also used as lookup keys, helper×all pairs add O(n²·t) = O(t^{5/3}) forms. All of this is o(q) at t ≈ √q. |
| Useful-hit filter | Stopping only on useful hits can only increase T, so bounding P(any hit or exception ≤ t) is conservative. |
| Integral | Using P(T>t) ≥ 1 − (0.4t² + C·t^{5/3})/q and integrating to s = 1.581√q (below the 3√q cap) gives (2/3)·s = 1.0541√q. The error term is ∫t^{5/3}/q = O(q^{1/3}), and discretisation is O(1). Only a first-moment union bound is used; no Poisson or independence assumption is needed. ✓ |

## Required qualifications

1. **(H1) is not optional.** If the enumeration runs out before about 1.58√q keys, the integral stops early. The bound then needs the fallback cost added explicitly; otherwise a tiny-n design could escape it. This also fixes n ≈ (4.74√q)^{1/3} ≈ 1.68·q^{1/6}.
2. **The order matters.** Ordering by newest vertex is what guarantees that any prefix spans at most m+1 vertices with t ≥ 2C(m,3). A lexicographic order by smallest index can touch all n vertices at small t, and then 32·C(n,6) is far larger than t². The record should say "newest-vertex layered order".
3. **Scope.** For a general triple hypergraph on V vertices the same count still holds (N ≤ 32·C(V,6) + O(V⁵)), but it is useless unless t is about 2C(V,3). So this says nothing about sparse, weighted or adaptive hypergraphs, correlated seed factories (Sol card proposal 3), or different detectors.
4. **The bound is deliberately weak.** A heuristic intensity of at most 0.4·t²/q would suggest a mean of about 1.40√q, but that needs second-moment control. Do not record 1.40.
5. **What it is not.** It is not a runtime dominance result or a lower bound for any other ECDLP method. Setup of about q^{1/6} scalar multiplications plus about q^{1/3} cache additions only makes the candidate worse; it isn't needed for the conclusion.

**Disposition:** record proposal 2 (cached-pair three-seed hyperedges), dense complete-triple instance only, as falsified on expected key count, with (H1)–(H3) stated. The sparse-hypergraph question stays open and untested.
