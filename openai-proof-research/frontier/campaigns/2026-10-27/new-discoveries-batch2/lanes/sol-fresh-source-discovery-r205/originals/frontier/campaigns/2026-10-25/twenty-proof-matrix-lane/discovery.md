# Matrix-lane discovery and completed outcomes

Date: 2026-10-25. Assigned lane only. No agents spawned; no shared index, other lane, dependency source, Git staging area or commit changed. No paper PDF generated.

## Outcome count

**Two distinct MathDB questions now have complete local Lean certificates.** Count each question once, not each lemma. Neither is MathDB336488. The historical audit separately found **0/19 full-main-theorem Lean proofs** in R023–R041; all nineteen accepted records describe scoped supporting formalizations. See [historical-audit.md](historical-audit.md).

| Rank | Question | Exact ID | Outcome | Novelty boundary |
|---|---|---|---|---|
| 1 | [MathDB362146: permutation-like eigenvalues](https://mathdb.com/p/362146/the-eigenvalue-conjecture-for-permutation-like-matrices) | `67a04085-8dd9-4158-a8b4-f7b2324c744d` | Full proof over every field and finite index set; zero or roots of unity, and zero iff not a permutation matrix | Elementary finite-semigroup argument; new to this project search, no worldwide priority claim. The source already proves the zero-eigenvalue part. |
| 2 | [MathDB340783: fair-discrepancy propagation](https://mathdb.com/p/340783/the-fair-discrepancy-propagation-conjecture-for-fully-balanc) | `88c8529c-45dc-484e-b014-26cd054e51f0` | Full counterexample certificate, all positive tolerances, every reflexive energy-comparison relation | **Existing counterexample credited to Shivam Patel.** New local formal verification, not a new disproof. |

The two build receipts audit **20** and **30** declarations respectively. These are **two outcomes**, not fifty. Formal reproducibility and source fidelity have been checked locally, but neither new artifact has an independent-agent review or parent acceptance. Do not silently equate this delivery with a project-wide total of twenty accepted outcomes.

## Exact statements

### MathDB362146

Let d>1, and let A be a square matrix with entries zero or one and exactly one 1 per column. Each eigenvalue is zero or a root of unity. Zero is an eigenvalue precisely when A is neither a permutation matrix nor the identity. The identity is already a permutation matrix, so the last exclusion is redundant. This is Definition 2.1 and Conjecture 5.2 of Lippold, *Permutation-Like Matrices*, arXiv:2403.02478v1.

The formal theorem is stronger in scope: arbitrary field K and arbitrary finite index type, including the requested complex and characteristic-zero cases. `exact_mathdb_conclusion` states both conclusions with mathlib's `Module.End.HasEigenvalue`. The predicate for a permutation matrix requires one unit entry per row and column and zero otherwise. No matrix invertibility, eigenvalue condition, eventual periodicity, or source conjecture is assumed in the proof.

For the proof, associate the finite function f sending each column to its 1-entry row. Matrix multiplication agrees with function composition. Two powers of f coincide by the finite pigeonhole principle. For Av=μv, v≠0, this yields μ^p=μ^q for p<q; if μ≠0, divide to obtain μ^(q−p)=1. A collision f(i)=f(j), i≠j gives the zero eigenvector e_i−e_j. When f is injective, it is bijective and the inverse function gives a matrix inverse. This also proves the exact permutation criterion.

Files: [Lean proof](permutation-spectrum-362146/formal/PermutationSpectrum.lean), [type and axiom checks](permutation-spectrum-362146/formal/Checks.lean), [build receipt](permutation-spectrum-362146/formal/build/audit.json), [full proof and source notes](permutation-spectrum-362146/README.md), [paper source](permutation-spectrum-362146/paper/main.tex).

### MathDB340783

For a nonzero real n×m matrix, the source calls it fully balanced when all row energies are approximately equal and all column energies are approximately equal. Energies are sums of squared entries. For ε>0, it asks whether having every entry of one row within ε of that row's arithmetic mean forces the same for all rows. This is Agama–Kibiti, *Balanced matrices*, arXiv:1810.07542v3, Definition 3.1, Conjecture 6.6 and Remark 6.7.

The positive matrix with rows (5,5,5), (1,5,7), (7,5,1) has all six energies equal to 75. Its first row has zero discrepancy; its second row's first deviation is 10/3. Scaling by ε gives a counterexample for each ε>0. The source leaves `≈` undefined, so the formal development proves exact balance, every positive absolute energy tolerance, and, most generally, the counterexample for every reflexive relation on energies. Thus the ambiguity is explicit rather than hidden in a definition. Equality is included in the source's own examples; no interpretation excluding equality is claimed covered.

The matrix and scaling were already posted by **Shivam Patel**, reply `be21f974-e069-4a4c-b446-252e228a1119`, on 2026-08-22T07:49:47.568226Z. The complete reply was read in the API response before implementation. Its mathematical content receives credit. This lane contributes a complete Lean certificate and explicit semantic treatment.

Files: [Lean proof](fair-discrepancy-340783/formal/Discrepancy.lean), [type and axiom checks](fair-discrepancy-340783/formal/Checks.lean), [build receipt](fair-discrepancy-340783/formal/build/audit.json), [full proof and source notes](fair-discrepancy-340783/README.md), [paper source](fair-discrepancy-340783/paper/main.tex).

## Screening and prior-solution checks

The live matrix-theory API returned **79/79 records**. All list titles/excerpts were screened; eight exact record responses were fetched. Only the two above were selected for work. MathDB336488 was excluded as instructed.

| Other screened exact record | Decision |
|---|---|
| 340782, interior balanced submatrix | Not selected: “interior” is insufficiently precise in the API statement; avoid an easy but potentially vacuous 1×1-submatrix argument. |
| 336487, norm-one dominant eigenvectors | Not selected: normalization conventions in the original computational claim require special care. |
| 336489, dominant-eigenpair scaling | Not selected: lower priority than an unrelated full spectral assertion. No outcome claimed. |
| 351542, rank-two permanent inequality | Not selected: exact source domain and sign hypotheses need further primary reading; no disproof claimed from the API's unqualified formulation. |
| 369712, constant-rank nilpotent affine-space dimension | Not selected: substantial geometry and a “sufficiently large field” condition; no short exact proof identified. |
| 373375, E0_2 determinant/inverse | Not selected: source-specific class must be developed; no proof claimed from the excerpt. |

Primary reading for the selected questions included the versioned HTML for both papers and the balance PDF text. For Lippold, Definition 2.1, Proposition 2.1, Section 4.2 (Corollary 4.5, Proposition 4.2, Proposition 4.4, Corollary 4.7), and Conjecture 5.2 were read. The paper explicitly says the zero-eigenvalue part is already answered. For balance, Definition 3.1, its equality examples, Conjecture 6.6 and Remark 6.7 were read. The API also exposes the prior full reply. No source theorem is imported as a Lean axiom.

Live web searches on 2026-10-25 included `"Permutation-Like Matrices" eigenvalues conjecture`, `"permutation-like" eigenvalues "roots" 2025`, `"2403.02478" conjecture eigenvalues proof`, `"fair-discrepancy" "balanced"`, and `"fair-discrepancy" counterexample`. They surfaced the primary papers and the known MathDB counterexample; no independent all-dimensional permutation-spectrum solution was located in this bounded search. This is not a novelty certificate.

A repository-wide text search of Markdown, Lean, TeX, JSON and text, excluding dependencies and this lane, found no substantive prior occurrence of the two questions. The one raw hit is an unrelated long integer containing `340783` in an older diagnostic JSON. The search receipt is [sources/project-duplicate-search.json](sources/project-duplicate-search.json).

## Reproduction and trust boundary

Run each `formal/rebuild.py`, or run [verification/rebuild_all.py](verification/rebuild_all.py). Both rebuild scripts reuse the existing premagic certificate's pin checks, dependency paths, fresh local build directory and axiom allowlist. They compile with `warningAsError=true`. They reject forbidden proof tokens and incomplete type/axiom inventories. Lean 4.34.1 and mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` are pinned. Standard axioms only: `propext`, `Classical.choice`, `Quot.sound`. Supplied compiler and precompiled dependency objects are trusted, not rebuilt or authenticated from scratch.

[Independent rational diagnostics](verification/independent-checks.json) validate the witness at four scales, reject a changed energy entry, and check all 288 finite function matrices in dimensions 1–4 for the power-composition and kernel/injectivity relations. These bounded checks supplement the universal Lean proofs; they are not counted as extra outcomes.

Source bodies are retained locally for provenance and keep their third-party rights. [sources/source-manifest.json](sources/source-manifest.json) records URLs and SHA-256 hashes. No upload, publication, PDF generation, shared-index update, Git staging or commit was performed.
