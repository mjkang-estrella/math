# Independent review: graph-normalization adjacency inequality

Review date: 2026-10-25. Target: **MathDB 349070**, canonical `outcomes/graph-normalization/` only. I read `openai-proof-research/AGENTS.md`, the pinned-repository provenance and catalogue, the complete canonical Lean source, `PROOF.md`, `main.tex`, metadata and reproduction instructions, the original and later-paper HTML in sibling `../graph-normalization-lane/sources/`, and the full archived MathDB record. This review does not re-audit other campaign outcomes or upstream theorems. Only this assigned review file was written. No nested agents, Git commands, local proof-object writes, or PDF build/render operations were used.

## Verdict and counting eligibility

**PASS — mathematics, full formal coverage, source correspondence, and manuscript consistency.** The result proves the entire inequality in the source's Conjecture 8.1, equation (19), with its actual normalized vector, and strengthens it from connected graphs to arbitrary finite simple undirected graphs. There are no mathematical or formal gaps in the reviewed artifacts.

**Eligible for exactly one full source-problem outcome**, under the campaign's stated policy permitting complete formal verification of known results. The eight local declarations, the general matrix lemma, and removal of connectivity are not additional outcomes. This is **zero demonstrated new-to-literature mathematical results** and must not be advertised as a newly resolved open problem: Guigues's 2026 Appendix B already uses a stronger diagonal-majorization inequality that implies this one. No priority of the Lean formalization has been established either.

**Release completeness at review time: FAIL / pending parent integration**, solely because the canonical package still has candidate status and does not yet contain the independent review and its hash bindings. This does not change the mathematical PASS or one-outcome eligibility. The parent must integrate this review, finalize metadata, and confirm the current-hash PDF build/render before final release certification. Details are below.

## Exact reviewed artifacts

Paths in this table are relative to the canonical `outcomes/graph-normalization/` directory. Hashes were recomputed after the substantive review to exclude a concurrent source change.

| File | SHA-256 |
| --- | --- |
| `formal/GraphNormalization.lean` | `7145ba2d825740ed68c00387b192b62b289a63aa4f84e7a1acf49e997b1f1e7c` |
| `PROOF.md` | `a802d21140a0cdca0687e3ed3ad384d575b9964b775b2f6a7376717a3837a8dd` |
| `main.tex` | `0aee5798e13f0e8c1121eae9df0e25a7457a5e81917a56bb57c1fae16a97143b` |

## Original source and exact target

I inspected the actual archived HTML of Laurent Guigues, [*Concerning Iterative Graph Normalization and Maximum Weight Independent Sets*, arXiv:2012.07764v1](https://arxiv.org/html/2012.07764v1#S8.E19), Section 8.1, **Conjecture 8.1**, equation **(19)**. It quantifies over the adjacency matrix `A` of a connected simple graph and every strictly positive real vector `x`, defines componentwise division

\[
y=x\oslash((A+I)x),\qquad
 y_i=\frac{x_i}{\sum_j(A+I)_{ij}x_j},
\]

and asks for

\[
y^T(A+I)y\leq\lVert y\rVert_1.
\]

The definition of `y` occurs immediately after the numbered inequality. The target is not the generally false inequality with an arbitrary unnormalized vector substituted for `y`. The reviewed Lean statement uses precisely the source's division by the full closed-neighborhood row action, including the diagonal contribution `x_i`.

The canonical `source.json` agrees field-for-field, for every retained field, with both inspected full MathDB 349070 snapshots (`queued-sources/349070.json` and the sibling `next-discovery-lane/sources/349070.json`). Those snapshots contain no posted solutions and label the conjecture open; this is historical database metadata, not evidence of current mathematical novelty. The canonical prose correctly supersedes that implication with explicit later-prior-art attribution.

Recomputed HTML hashes match both `primary-reference.json` and the lane's `sources/manifest.json`:

| Local source in `../graph-normalization-lane/sources/` | SHA-256 |
| --- | --- |
| `source.html` | `20c02aaf58f7cf58c5dd69efa1050fe1942460930fc0362dff1fb18f78c63469` |
| `prior-2026.html` | `53fb5493b1841d7861518f611b5c02daf68d53b3505d9cd0da6d0a213fbc47ca` |

## Independent mathematical verification

Let `B` be any finite real symmetric matrix with entrywise nonnegative coefficients. Let `x_i ≥ 0`, put `s_i = ∑_j B_ij x_j`, and assume `s_i > 0` for every index. No positive-semidefiniteness, irreducibility, connectivity, or spectral assertion is needed.

For arbitrary real `a_i`, nonnegativity of `B_ij x_i x_j (a_i-a_j)^2` gives

\[
2B_{ij}x_ix_ja_ia_j
\leq B_{ij}x_ix_j(a_i^2+a_j^2).
\]

Summing over all ordered pairs and exchanging indices in the second square term, using `B_ij=B_ji`, yields

\[
\sum_{i,j} B_{ij}(x_i a_i)(x_j a_j)
\leq \sum_i x_i a_i^2 s_i.
\]

Substitution `a_i=1/s_i` is legitimate by the stated row positivity. The left side becomes `y^T B y` with `y_i=x_i/s_i`; each right summand is exactly `x_i/s_i=y_i`. This proves `y^T B y ≤ ∑_i y_i`. It remains valid with zero coordinates of `x` when the row-action hypothesis holds. No cancellation by `x_i` is used, and no strict positivity of `x` is silently required for this general lemma.

For the graph specialization, `B=A+I` has nonnegative entries, is symmetric, and has diagonal entries one because the graph is simple and loopless. For strictly positive `x`, the diagonal summand proves `s_i ≥ x_i > 0`. Therefore all `y_i > 0` and `∑_i y_i = ∑_i |y_i| = ‖y‖₁`. This completes the source assertion. The argument works unchanged for disconnected graphs, isolated vertices, singleton graphs, and vacuously the empty finite type. Strict positivity of `x` is preserved from the source rather than replaced by an unstated convention for `0/0`.

## Independent Lean compilation and all eight declarations

I ran the specified executable:

`/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean -DwarningAsError=true --stdin`

with working directory `/tmp`. Standard input was the **complete canonical source**, followed by `#check GraphNormalization.name` and `#print axioms GraphNormalization.name` for every locally declared definition or theorem. The source was not imported as a compiled module. No `-o` argument was supplied, and no source-adjacent or development-lane `.olean` was on the search path or used. The canonical `formal/` directory contained no `.olean` at inspection time.

`LEAN_PATH` was explicitly replaced with only the `.lake/build/lib/lean` directories of `mathlib`, `plausible`, `LeanSearchClient`, `importGraph`, `proofwidgets`, `aesop`, `Qq`, `batteries`, and `Cli` below:

`/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages`.

The compiler reports **Lean 4.34.1**, release commit `5045d0056413266e57c625dcd7c365b10e377c52`. The campaign's `pins.json` and that formal project's `lake-manifest.json` agree on mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` and all eight other dependency revisions. In accordance with the no-Git instruction, I did not independently establish checkout cleanliness or revisions with Git. The verified claim is compilation against the supplied dependency artifacts with matching recorded pins.

**Result: exit 0, empty stderr, all 8/8 declaration checks and axiom reports present.** There is one noncomputable definition and seven theorems; no local abbreviations or lemmas were omitted from the inventory.

| Declaration in `GraphNormalization` | Check | Axioms |
| --- | --- | --- |
| `symmetric_energy_le` | PASS | `propext`, `Classical.choice`, `Quot.sound` |
| `normalized_energy_le` | PASS | `propext`, `Classical.choice`, `Quot.sound` |
| `closedKernel` | PASS | `propext`, `Classical.choice`, `Quot.sound` |
| `closedKernel_nonneg` | PASS | `propext`, `Classical.choice`, `Quot.sound` |
| `closedKernel_symm` | PASS | `propext`, `Classical.choice`, `Quot.sound` |
| `closedKernel_eq_adj_add_one` | PASS | `propext`, `Classical.choice`, `Quot.sound` |
| `graph_normalization_inequality` | PASS | `propext`, `Classical.choice`, `Quot.sound` |
| `mathdb349070` | PASS | `propext`, `Classical.choice`, `Quot.sound` |

The canonical source contains no `sorry`, `admit`, custom `axiom`, `unsafe`, or `native_decide`. The axiom audit confirms that no hidden admitted theorem or assumed normalization bridge enters any of these declarations. The independent result agrees with the existing eight-declaration audit receipt but does not rely on that receipt.

### Formal bridge to actual adjacency, matrix multiplication, and L1

I also inspected mathlib's definitions in `Mathlib/Combinatorics/SimpleGraph/AdjMatrix.lean` and `Mathlib/Data/Matrix/Mul.lean`. `G.adjMatrix ℝ` is one on adjacency and zero otherwise; `Matrix.mulVec` takes a row's dot product with the column vector; `dotProduct` sums entrywise products.

`closedKernel` is one exactly when `i=j` or `G.Adj i j`. `closedKernel_eq_adj_add_one` proves an actual equality with `G.adjMatrix ℝ + (1 : Matrix ι ι ℝ)`. The diagonal case uses looplessness; off the diagonal it is exactly the adjacency entry. Thus the identity matrix has not been confused with an all-ones matrix, and the bridge is proved rather than assumed.

`graph_normalization_inequality` proves row positivity by the diagonal summand using `Finset.single_le_sum`. It instantiates the general matrix theorem and proves the absolute-value conversion by positivity of each quotient. Finally `mathdb349070` rewrites the proved kernel equality and unfolds actual `Matrix.mulVec` and `dotProduct`. Its checked conclusion is

```lean
let B := G.adjMatrix ℝ + (1 : Matrix ι ι ℝ)
let y := fun i => x i / (B *ᵥ x) i
dotProduct y (B *ᵥ y) ≤ ∑ i, |y i|
```

Its only substantive inputs are an arbitrary finite simple graph and `∀ i, 0 < x i`. The decidability instances are computational instances, not graph restrictions. There is no connectedness assumption or imported hypothesis asserting the desired energy bound. Expanding the checked matrix product gives exactly `∑_i∑_j B_ij y_i y_j`, and the right side is the finite real L1 sum. Writing the norm as this sum rather than using a separately bundled normed-space type is exact mathematical coverage.

## Prior art and manuscript agreement

I inspected [Guigues, *Graph Normalization: Fast Binarizing Dynamics for Differentiable MWIS*, arXiv:2605.05330v1](https://arxiv.org/html/2605.05330v1#A2), **Appendix B**, “Proof of Theorem 1 (Strict Energy Descent),” item 2, **Global Dominance**, paragraph `A2.I1.i2.p1`, formula `A2.I1.i2.p1.m2`. It explicitly uses, for symmetric nonnegative `B`,

\[
z^TBz\leq\sum_i\frac{(Bu)_i}{u_i}z_i^2
\]

with positive reference vector `u` (its notation is `y^k`) and nonnegative test vector `z` (its notation is `y`). In that appendix `B=I+γA`; choosing `γ=1` gives the source's matrix. Setting `u=x` and `z_i=x_i/(Bx)_i` reduces the right side to `∑_i x_i/(Bx)_i`. Thus the prior displayed bound already implies the entire graph-normalization inequality. The appendix attributes its diagonal-majorization lemma to reference [36], Lee and Seung (2000); this review does not claim to have independently audited that older paper.

The complete `main.tex` and `PROOF.md` agree on all mathematical hypotheses, the weighted Young proof, the normalized substitution, denominator positivity, the finite L1 identity, and the arbitrary-graph strengthening. The TeX's description of the general matrix case is read with the explicitly stated `x_i ≥ 0` from its lemma. Its bibliography identifies both versioned arXiv sources, and its discussion correctly says the prior inequality yields this result.

Both documents explicitly characterize the work as a formal verification of a standard majorization consequence and disclaim mathematical novelty. Both restrict the conclusion to the inequality and disclaim iterative convergence claims. In particular this review certifies neither convergence of iterated weight vectors, convergence to a maximum independent set, nonlinear-activation behavior, nor the later paper's broader energy/convergence arguments. Nothing in the proof requires endorsing those claims. No numerical experiments are needed for this universal proof.

## Minor package and reproducibility findings

1. **Independent-review integration remains pending.** At inspection, canonical `outcome.json` still says `candidate`, `README.md` says it awaits independent review, and no canonical `review.md` is present. `main.tex` advertises an included independent review. The parent should copy/integrate this review, record the reviewed Lean and TeX hashes above, update the status/readme consistently, and only then package. These are expected finalization tasks, not proof defects.
2. **The checked-in outcome is not yet the extracted release.** The advertised `verify_outcome.py`, `build_paper.py`, and `pins.json` live at campaign level until `package_outcome.py` copies them into a release. The README correctly distinguishes release-root commands from the checkout's `../../verify_outcome.py`; their current absence within the outcome is not itself a defect. I did not run that verifier because it invokes Git and writes build outputs; the independent stdin check above supplies the requested proof audit. No extracted archive was independently rebuilt in this review.
3. **Source provenance is referential.** The two HTML files remain in the sibling development lane; the canonical package retains versioned URLs and matching hashes rather than redistributing those full third-party texts. This is consistent with `RIGHTS.md`, but source inspection from an extracted release requires retrieving the cited versions. The MathDB `open` status should remain recognizable as historical provenance, never promoted into an up-to-date novelty claim.
4. **Build receipts match, but rendering is reserved to the parent.** The existing canonical `build/audit.json` binds the exact reviewed Lean hash and eight declarations. `build/paper-build.json` reports exit 0, no issues, an existing PDF, and TeX hash `0aee5798e13f0e8c1121eae9df0e25a7457a5e81917a56bb57c1fae16a97143b`, which matches this review. I did not build, render, or visually inspect the PDF; the receipt alone is not my visual-layout approval. Rebuild/review bindings are needed if either reviewed source changes.
5. **Dependency verification limit is explicit.** The recorded manifest and pins agree, and independent Lean checking succeeded. No Git-based dependency-cleanliness verification was performed under the user's prohibition. Final release tooling may perform its own permitted pin/cleanliness checks; this review must not be represented as already doing so.

**Final recommendation: PASS for the exact full source assertion and its complete Lean certificate; accept as one known-result formal-verification outcome after the parent's review integration and current-hash build/render confirmation. No mathematical gaps, no new mathematical novelty claim, and no iterative-convergence claim.**
