# Mathematics research

This repository collects AI-assisted mathematical research, written proofs, Lean
formalizations, and computational checks. Its main collection is a campaign on
problems listed as open on MathDB. It also contains preprints that build on
manuscripts from OpenAI's mathematics research collection.

## MathDB results

As of the November 23, 2026 audit, **105 results (86 proofs and 19 refutations)**
have a kernel-checked Lean statement and passed adversarial review by a separate
AI model. The audit removed five results from the
previous count of 110 after finding earlier solutions or short derivations from
published work. [Audit and counting criteria][claim]

| Results | Evidence |
| --- | --- |
| **105** | Passed adversarial review and the campaign's prior-art and substantiality checks. |
| **52** | Additional Lean-checked results, mostly counterexamples found by quick computational searches. |
| **5** | Additional Lean-checked results for statements as printed in the cited papers, where the MathDB records misstate them. |

The reviews were performed by AI models. The literature search had limited
coverage, including some inaccessible journal texts. Lean checks the stated
formal theorem. Some results use a cited theorem or a written argument to
connect that statement to the original problem. The evidence table records
these dependencies and caveats for each result. [Row-by-row evidence][evidence]

### Selected results

| MathDB | Result |
| --- | --- |
| [321730][locating] | The locating chromatic numbers of the Cartesian products of a complete graph with a cycle and with a path agree for complete graphs of order at least 7 and paths and cycles of order at least 4. |
| [344334][littlewood] | Among pairs `(k, n)` with `1 ≤ k ≤ n − 1`, the only inadmissible Littlewood pairs are `(2, n)` and `(n − 2, n)` for `n ≡ 1 (mod 6)` and `n ≥ 13`. The Lean statement uses five explicit hypotheses from the source paper. |
| [361006][spherical] | Proper rational spherical triangles fall into the known two-right-side family and eight sporadic triangles. Lean checks the classification of the rational solutions of L’Huilier’s equation. |
| [366504][poisson] | The derivation construction for transposed Poisson 3-Lie algebras fails over fields of characteristic zero. |

### Find and verify a proof

- Use the [MathDB proof index][index] to find the written proof and Lean source
  or compressed Lean appendix by problem ID. The index also records withdrawals.
- Use the [evidence table][evidence] to find the precise theorem statement, Lean
  declaration, replay record, and prior-art caveats.
- See the [review and replay procedure][replay] for the checks applied to each
  package. Large certificate appendices have their own decompression notes.
- The [campaign ledger][ledger] preserves the acceptance history, including
  entries later withdrawn from the audited count.

## Manuscripts

Each package gives the theorem scope, source dependencies, and available
PDFs, LaTeX sources, and build or verification instructions.

| Area | Manuscript packages |
| --- | --- |
| Number theory | [Factor-count residues and Poisson–Dirichlet limits for prime predecessors](openai-proof-research/publications/prime-predecessor-residues/README.md), conditional on the analytic estimates stated in the paper |
| Analysis and geometry | [Complete Crouzeix equality in dimension four](openai-proof-research/publications/complete-crouzeix-equality/README.md), [complete Crouzeix equality without scalar compression](openai-proof-research/publications/entangled-crouzeix-equality/README.md), [nonlinear curl coefficient extraction](openai-proof-research/publications/nonlinear-curl-coefficients/README.md), [conditional logarithmic Brunn–Minkowski stability](openai-proof-research/publications/logarithmic-brunn-minkowski-stability/README.md), [ball–tube and ball–slab nesting costs](openai-proof-research/publications/nested-isoperimetric-contact/README.md), [tetrahedral cylinder covers](openai-proof-research/publications/tetrahedral-cylinder-bound/README.md) |
| Probability and combinatorics | [Binary-information contraction stability](openai-proof-research/publications/binary-information-stability/README.md), [Gaussian propeller stability](openai-proof-research/publications/gaussian-propeller-stability/README.md), [rooted entropy for perfect matchings](openai-proof-research/publications/rooted-matching-entropy/README.md), [four-state reconstruction with variable edge channels](openai-proof-research/publications/variable-channel-capacity/README.md) |
| Quantum algorithms | [Exact discrete logarithms from a flagged polygonal transform](openai-proof-research/publications/exact-fixed-gate-logarithms/README.md), under the interfaces stated in the paper |

## Other research

- [Multiplicative persistence](persistence-research/README.md) reduces the
  persistence-12 question to a search over 7-smooth integers and records
  exhaustive finite searches and their audits. The global conjecture remains open.
- [Factoring](factoring-research/README.md) and [discrete logarithms](dlp-research/README.md)
  contain algorithm specifications and bounded experiments. Both projects
  ended without a verified asymptotic improvement. The [research monitor](research-monitor/README.md)
  shows the discrete-log work estimate and its assumptions.

## Upstream sources and citations

The OpenAI manuscripts used as inputs are pinned to
[`openai/math@fd4aeeb`][upstream-pin]. The [source catalogue](openai-proof-research/sources/CONTENTS.md)
and [source guide](openai-proof-research/sources/README.md) record the upstream
manuscripts and the pinned revision. See [OpenAI's upstream collection][upstream]
for its manuscripts and formalizations.

When citing a result, use the individual manuscript and its version or DOI when
available. For a MathDB result, cite the problem ID and the repository revision
that contains the proof.

[upstream]: https://github.com/openai/math
[upstream-pin]: https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
[claim]: openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/public-claim-100/CLAIM-WORDING.md
[evidence]: openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/public-claim-100/CLAIM-EVIDENCE.md
[index]: openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/mathdb-submissions/INDEX.md
[ledger]: openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ledger.json
[replay]: openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/root-intake-r60/FABLE-PIPELINE.md
[locating]: openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/mathdb-submissions/321730-locating-chromatic-complete-times-cycle/PAPER.md
[littlewood]: openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/mathdb-submissions/344334-littlewood-inadmissible-pairs/PAPER.md
[spherical]: openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/mathdb-submissions/361006-rational-spherical-triangles-classification/PAPER.md
[poisson]: openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/mathdb-submissions/366504-transposed-poisson-derivation-construction/PAPER.md
