# R028 — Two Seymour vertices in every sink-free oriented graph

**Accepted as the sixth substantial result of the 2026-10-14 campaign: 6/10.**
Acceptance is internal, under the explicitly stipulated pinned source premises;
it is not external peer review or certification of worldwide priority.

Assume the ordinary Seymour theorem and finite-relation pruning lemma stated
in the paper from OpenAI/math revision
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Every nonempty finite oriented
graph without a sink has two distinct vertices v with
`|N₂(v)| >= |N₁(v)|`, where N₂ means directed distance exactly two.
There are no additional degree, connectivity, order or missing-edge restrictions.

The conclusion is Dara–Francis–Jacob–Narayanan Conjecture 2. The new deduction
retains the exceptional boundary after deleting a hypothetical unique good
vertex, then aggregates the gains of compatibility-selected fibers in a
transitive blowup. The strict gain closes the credited pruning objective.
Subset deletion, products and pruning remain credited antecedents; the
contribution comparison is bounded.

The [nine-page manuscript](../campaigns/2026-10-14/seymour-s2-manuscript-r1/output/pdf/main.pdf)
has SHA256 `e8039480ad15393021dc46a5a2547bb09763a30de16d863a26f173ac4cbac598`.
The frozen full candidate and scope are unchanged. Independent gates:

- [Proof](../campaigns/2026-10-14/seymour-s2-proof-r1/review.md): PASS_FULL_S2.
- [Contribution](../campaigns/2026-10-14/seymour-s2-contribution-r1/review.md): CONTRIBUTION_PASS_SUBSTANTIAL.
- [Formal support](../campaigns/2026-10-14/seymour-s2-formal-review-r1/review.md): PASS_SCOPED_FORMAL.
- [Manuscript](../campaigns/2026-10-14/seymour-s2-manuscript-review-r1/review.md): PASS_MANUSCRIPT, no required repairs.

**The full graph theorem is not formalized.** Eleven Lean supporting theorems
cover integer boundary implications, finite-family aggregation, cardinality
and conditional complement/pruning consequences. Seven author controls and
seven independent controls expose false weakenings. Minimality, graph
identities, connectivity, blowup bounds, anchor exclusions and pruning
existence/admissibility remain in prose. A fresh build from the release
extraction passed with Lean 4.34.1 and pinned mathlib, standard axioms only.

The [final release](../campaigns/2026-10-14/seymour-s2-release/README.md)
contains 228 files including its manifest. Archive
`output/release/r028-two-seymour-vertices-v1.zip` is 355,950 bytes, SHA256
`3be40a44a6b4722bb155ccc2b96461a1ad6df5e50dca8ec48775c05a9248dabd`.
Bundle manifest SHA256 is
`77a534508736ffc608f8f27f6b75a26a04dc67952f0a5c481e46abaf0c3831e7`;
final gate SHA256 is
`4e938245c237c7f1f74a6951519d79f296e2a672c4f612026d046ddd7ffa8667`.

Parent verification passes archive and clean-extraction integrity, portable
finite diagnostics, byte-identical reassembly, fresh Lean compilation,
and wrong-anchor, changed-gate, missing-file, extra-file and symlink rejection.
The independent manuscript audit additionally passed nineteen public-package
scenarios, an isolated replay and a byte-identical PDF rebuild; all nine pages
were visually inspected. These diagnostics and hashes do not replace the
universal proof. See the [final receipt](../campaigns/2026-10-14/review-entry-parent/s2-final-package-verification.json).

Author: Myeongjin Kang, no affiliation. Original prose CC BY 4.0; original code
MIT. Public submission is authorized and being prepared; this acceptance record
does not assert an upload, DOI or external acceptance. Earlier frozen pending
metadata remains historical. Research continues toward 10/10.

## Public publication

Published 2026-10-17 UTC: [Zenodo manuscript and supporting package](https://zenodo.org/records/23430050), DOI `10.5281/zenodo.23430050`; [MathDB paper](https://mathdb.com/abs/2610.00028). Files and metadata were verified; see the [submission receipt](../campaigns/2026-10-14/submissions/README.md). Earlier pending-submission statements above record the acceptance-time state. Publication does not imply external peer review.
