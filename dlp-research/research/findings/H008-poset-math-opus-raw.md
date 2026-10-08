# H008 new hyperplane paper: raw Opus mathematics review

Provider claudeAgent, model claude-opus-5-5; request
ecdloop-h008-poset-math-opus-20261008-r1. Raw claims await root reconciliation.
In particular adaptive/restart lower bounds and probability/conditioning details
are not automatically accepted as theorems. Reviewer ran exact binomial arithmetic
for source-table checking, no synthetic ECDLP solver experiment or repo edit.

I read both versions of arXiv:2607.09814 in full (v2 PDF text plus HTML formula markup, and v1 for comparison). The paper does not improve on the baseline: verified improvement stays **NONE**. Its probability claims overcount the same candidates 100–200×. Once corrected, the method needs on the order of p/log p work, against about √p for rho.

The repo was not touched. The downloads are in `/tmp/gd_src*` and `/tmp/gd_*.txt`. The only computation was exact binomial arithmetic to check the paper's Table 2.

**Sources**
- v2, Aug 6 2026 (Mahalanobis): https://arxiv.org/abs/2607.09814v2, PDF https://arxiv.org/pdf/2607.09814v2, HTML https://arxiv.org/html/2607.09814v2
- v1, Jul 10 2026: https://arxiv.org/pdf/2607.09814v1
- Earlier work behind the old H004/H006 audits: https://arxiv.org/abs/2310.04132 and Cheng https://arxiv.org/html/cs/0507026

**What changed from v1 to v2.** v1 said the attack "has the potential to be a polynomial time algorithm", had an integer-only simulation algorithm, and gave a success formula without the factor for the number of b choices. v2 removes the simulation and adds three things:
- §5: a "Pollard rho on penultimate intersections" idea with Table 1.
- §6: the extra exponent C(ℓ′,d), which is where the overcount comes from.
- Table 2, where the author concedes the attack is "no better than exhaustive search".

## Exact algorithm

Notation: ℓ = 3n′ and ℓ = 2ℓ′. Take points P_i = n_iP and Q_j = −n_jQ, build the matrix M, and let K be its left kernel, shape ℓ×2ℓ, with the identity in anti-diagonal form on the Q columns.

1. **Guess.** Pick a random set a of ℓ′ dense (P) columns, independently of any values. Set K′ = row-reduce(K[a]^T) to anti-diagonal form. K′ is ℓ′×ℓ and its columns are indexed by Q points.
2. **Determine.** For every b ⊂ dense(K′) with |b| = ℓ′−d:
   - Compute T = leftker(K′[b]), which has dimension d.
   - Build the signature matrix A = (T·K′[Δ])^T, of size (ℓ′+d)×d, where Δ is the remaining columns.
   - For every (d−1)-row subset y of A, hash the normalised kernel line w_y.
   - A duplicate w_y = w_y′ with |y∪y′| = d means A[y∪y′] is singular. That gives K′[b∪x] singular, then a zero maximal minor of K (Theorem 1, converse direction), then the relation.

**Group-sum meaning (theorem).** This is the H006 equivalence applied here. The reduction steps are left-multiplication or Schur complements, so maximal-minor zero sets are preserved. Hence K′_R = 0 exactly when P_{a′} + Σ_R Q_j = O, i.e. Σ_{i∈a′} n_i ≡ m·Σ_{j∈R} n_j with |R| = ℓ′.
- So the method is a **one-sided enumeration of Q-subset sums against a fixed P-side sum**. Nothing is matched in the middle.
- **The useful coefficient is c_R = Σ_R n_j.** Resample if Σ_{a′} n_i ≡ 0, which is known in advance. After that, every hit automatically has c_R ≠ 0 and gives m = Σ_{a′} n_i / c_R.

**Correctness notes (theorem level, after fixes):**
- Theorem 1's "iff" is overstated. The forward direction needs the zero minor to use exactly the dense columns a. The algorithm only relies on the converse, which is sound.
- Theorem 4 writes Υ (size ℓ) where it means b.
- Algorithm 2 returns "No result" when |y∪y′| > d. That case is actually a success, because every d-subset of the union is singular. It is a negligible gap in completeness, not in soundness.
- Every "general position" failure is itself a zero-minor event, so it is a success if handled.
- **The pivots are chosen by index, not by value.** Pivot failures are either success events or events visible from the known n_i alone. So the old H006 concern about conditioning and value-dependent pivoting **does not bind for the main algorithm.** The real error is a different one.

## Probability: what is wrong and the repaired bound

**The flaw is multiplicity, not just correlation.** Over all b, one run tests exactly the family
F_a = {R : |R| = ℓ′, |R ∩ pivot(K′)| ≤ d}, with |F_a| = Σ_{k≤d} C(ℓ′,k)².

A candidate R with k pivot columns is counted C(ℓ′−k, d−k) times. By Vandermonde, the counts sum to C(ℓ′,d)·C(ℓ′+d,d), which is the paper's exponent. So the paper treats identical events as independent trials.

**Repaired bounds (theorems).** These hold in the algorithm's own randomness: m is arbitrary and nonzero, the n's are uniform, and distinct sampling costs an extra O(ℓ²/p).
- Each event is the vanishing of a nonzero linear form with coefficient 1 on a′. Distinct R give non-proportional forms, so the events are pairwise independent, each with probability 1/p.
- With μ = |F_a|/p, one run succeeds with probability between μ/(μ+1−1/p) − O(ℓ²/p) and (|F_a| + ℓ² + ℓ′² + 2)/p.

**Checked against Table 2.** ℓ′ is not stated in the paper. I reconstructed it from the printed floor values; for 100-bit p it comes out as 60 or 61. Under every consistent ℓ′:

| Row | Paper's exponent counts each candidate | Paper's probability | Repaired range |
|---|---|---|---|
| 100-bit, d=17, ℓ′=61 | ~101× | ≈1 | 0.21–0.26 |
| 104-bit, d=18, ℓ′=60 | ~191× | ≈0.99994 | 0.048–0.051 |

The paper's printed probabilities don't reproduce exactly either, which is consistent with ℓ′ not being given.

**Cost (theorem, scoped to this algorithm).**
- Hash insertions per run satisfy H = C(ℓ′,d)·C(ℓ′+d,d−1) ≥ (d/(ℓ′+1))·|F_a|.
- More generally, each detected candidate needs two inserted subsets, so after h insertions at most (ℓ′+1)h/2 candidates are covered.
- Combined with the upper bound on success, the expected total insertions until success, over any restart policy, is **Ω(p/ℓ′)**. That is Ω(p/log p) for the paper's ℓ′ = O(log p).
- Making ℓ′ large doesn't help: writing down K′ alone costs Ω(ℓ′²), so total work is ≥ p/ℓ′ + ℓ′² ≥ Ω(p^{2/3}), still above √p.
- Memory per b is C(ℓ′+d, d−1) entries, about 2^53 in Table 2.

**What is actually new.** The inner hashing is the d-dimensional generalisation of the "row-ratio hashing" noted in H004 (the d=2 case). It saves a factor (ℓ′+1)/d, which is polynomial only. In Table 2 the b-overlap redundancy more than cancels it: 27–62 insertions per distinct candidate.

The method is dominated by H006's own corrected Mechanism A, which hashes group sums from two lists and gets Θ(√q).

## §5 rho on penultimate intersections

**Status: heuristic, and as stated unsupported.**
- No iteration function is specified.
- Penultimate lines live in P^{ℓ−1}(F_p). They coincide only through structural events of probability about 1/p each, so the birthday estimate √C(2ℓ,ℓ−1) does not apply.
- A useful coincidence needs two subsets that differ in one element. If the walk visits W subsets chosen without looking at values, success probability is ≤ ℓ²·W/p (theorem).
- If the walk hashes lines to indices, the random-function merges it finds are almost all useless: useful ones are about ℓ²/p of them (heuristic).
- For walks whose next step depends on line values, nothing is proved. The H006 conditioning objection applies here, and no lower bound follows, since the points themselves are part of the input.
- Table 1's comparison of log₂C(2ℓ,ℓ−1) with log₂p has no bearing on complexity.

## Cheap decisive falsifier

This needs arithmetic only, no simulation. For any Table 2 or 3 row and any ℓ′ consistent with it, compute U = (Σ_{k≤d} C(ℓ′,k)² + ℓ² + ℓ′²)/p. If U is below the printed probability, that probability is refuted. It is for every row I checked (U ≤ 0.41, against ≥ 0.93 printed).

To revive the algorithm, someone would have to either:
- detect more than (ℓ′+1)/2 candidates per hash insertion, which the collision rule rules out; or
- specify a value-dependent §5 walk with a proved rate of useful collisions.

A toy count of useful versus useless merges at small p could reject a specified walk, but small simulations cannot establish any asymptotic claim.

**Baseline:** generic rho, Θ(√q), stays the working reference.
