# T164F99 contribution review r1 — outside REPORT

Independent SUBSTANTIAL-CONTRIBUTION review, round 1, of the frozen arithmetic
r99 full author proof (family 164, FS union FP in every infinite field of any
characteristic, with the d | m finite-field corollary). Reviewer: Factory Droid /
claude-opus-5-5 / high, 2026-10-20. Conditional on correctness; no correctness
gate, acceptance, count, or priority is assigned here or in the packet.

## Verdict

**TECHNICAL** for the entire unchanged frozen scope (Theorem F and Corollary G).

The strongest integrated known reduction closes the full scope with only routine
operations: Alweiss's Proposition 4.1 / Section 5 mechanism (arXiv:2307.08901v6,
read in full) is transported by (i) substituting Bergelson–Leibman Corollary 7.11
(Annals 150, 1999; arXiv:math/9907201v1), a strictly stronger recurrence theorem
already valid over any infinite ring of any characteristic; (ii) replacing
rational-height budgets by finite sets obtained from Tychonoff compactness of the
coloring space — a device already written out in the pinned source 164's
`08_alignment.tex` (`lem:finite-word-plan` and the cylinder-set compactness
paragraph) in a strictly harder nilpotent setting, with the same compensating
scale update map; (iii) characteristic-free Ramsey/Folkman selection identical to
Alweiss Section 5 Steps II–IV and the pinned `lem:chain-selection`; (iv)
Hunter's Remark 1.1 distinctness device via an elementary 3-coloring of doubling
orbits plus an isolated zero color for characteristic 2; and (v) a standard
König compactness over F_{p^{j!}} for Corollary G at its exact divisibility-only
scope. That this substitution characteristic-frees a vdW-driven sum-product
proof is published practice: Moreira's Theorem 7.5 (arXiv:1605.01469v1) extends
to every field with "the only new ingredient ... a suitable version of the
polynomial van der Waerden theorem" from Bergelson–Leibman 1999. The remaining
operation after this reduction is careful, correct-looking bookkeeping of the
transport, which the author executed and documented; under the unchanged
campaign criteria (routine transport, classical/source composition and parameter
replacement do not count) this is TECHNICAL.

Not REDISCOVERED: no actual prior statement of Theorem F or Corollary G was
found. Alweiss v6's "arbitrary fields follow from Q by a standard compactness
argument (see [8])" cites Bowen–Sabok's first-order compactness, which as
written (their Corollary 1.2, Section 4.3) reaches only characteristic 0 and
characteristic > p0; it neither states the FS union FP pattern in small positive
characteristic nor supplies a proof covering it. Bergelson–Moreira/Moreira cover
two-variable {x, x+y, xy}-type patterns over all fields; Green–Sanders,
Shkredov, Cilleruelo, Kousek and Ackelsberg–Bergelson cover large-characteristic
or density variants. Not UNRESOLVED: the contribution comparison is resolvable
from body reads of the strongest methods; the bounded search limits (below) do
not open a genuine comparison gap. The small-characteristic case appears
genuinely open in the literature seen, but only within the recorded bounded
searches — no worldwide-exhaustive or priority claim.

Scope honesty: Corollary G gives d | m only, with no bound and no all-large-m
statement (e.g. F_{2^m}, m prime, is not covered); characteristic 0 was known
(Alweiss over Q + Hunter's remark); T164F99 does not resolve the structural r35
read-once positive-integer question.

## Anchors

Immutable author root `frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r99/`
(re-verified against the role-brief values; original scope freeze byte-identical
to the sealed copy):

- author FINAL.json SHA-256 `8bdd4b8849f96c24fca7c91c52006c1b9cb6ee2c6accb44d7e5628746c5ab54f`
- author packet MANIFEST.json SHA-256 `21ce5d125854250c90509dc0d9f4365fcceb97afc6e7e8faa510ea1e509d711e`
- author REPORT.md SHA-256 `bdb418b29258b2318310c8876a3beed40a8dc4271e2a1b7ec1d60c072ca6f065`
- frozen scope SHA-256 `2a39e2a3410a79812e3e48478fa892d507e163fcd739fd409173219c7c5a23b7`
- author proof SHA-256 `14d9cd60f44d0bbb8867159b013e7e3026b09cc73208cdce8d3f628dc7175847`

This review's packet (`packet/`, 80 files: public review/limits/rights/inputs/
search-log/verifier/controls/seal; private author/history/context copies, pinned
source 164 bodies blob-verified against the pinned 13223-entry tree, and
reviewer-acquired primary bodies):

- packet MANIFEST.json SHA-256 `b34cd9b865124317b73ceaf5b4f8e82fa778c6f83afa3b6ce05de2bf14917fe2`
- review (packet/public/review.md) SHA-256 `1d2f37422eabab1e0d47c83c42fd4a7caaa3c3afd11565ee0c6a20eb44d93e5b`
- reading limits (packet/public/reading-limits.md) SHA-256 `54ca7df1c56e8be5f5986358e05e4015b9ddca2652c84b213d3dfefa68bfdddb`

Detached seals at this root: FINAL.json (embeds the manifest/report/review
hashes and the author anchors above), FINAL.sha256, REPORT.sha256. Read-only
verifier `packet/public/verify.py`; copied-controls `packet/public/controls.py`
results in `artifact-controls.json`; unchanged-input check in `unchanged.json`.

## Limits

Read extents, versions, access failures and the full bounded search record are
in `packet/public/reading-limits.md` and `packet/public/search-log.json`.
Not obtained: Bergelson–Leibman–McCutcheon (2005), Green–Sanders and other
bodies, Kousek's journal version; MathSciNet/ZBMath inaccessible; Semantic
Scholar rate-limited for two of three citation queries. The verdict does not
depend on those gaps.
