# Solo algebra/matrix r2 — no eligible discovery nominated

**Credit requested: 0. Additional campaign count remains 0/30.** Root alone
reviews, integrates, and counts; no shared files were changed.

## Main finding

The two-step nilpotent clause of Heib–Bruschi's minimal-graph-admissibility
conjecture has complete ordinary counterarguments in this lane:

- `PROOF.md`: a generic 12-dimensional real or complex counterexample. The
  112 independent bracket coefficients cannot come from any of the polynomial
  charts for multiplicative bases, each with only 108 parameters.
- `PRIOR_METHOD.md`: an explicit rational 20-dimensional counterexample,
  obtained by the exterior-square version of a public 2016 rank obstruction.
  This second route exposes the strongest objection to discovery eligibility.

Exact target: [arXiv:2601.16161v2](https://arxiv.org/abs/2601.16161v2),
Definition 15, equation (6), printed/PDF p.7, Conjecture 91(a), p.62;
[MathDB 372720](https://mathdb.com/api/posts/372720). The definition requires an
actual basis, not a redundant spanning set. The two key PDF pages were rendered
and visually inspected; images are under `verification/`.

**Recommendation: do not count this as a genuine new discovery.** A
[2016 public answer](https://math.stackexchange.com/questions/1858832/does-every-finite-dimensional-real-nil-algebra-admit-a-multiplicative-basis)
already gives the closely corresponding symmetric-algebra rank obstruction.
The exterior-square transfer is short and complete. The public answer does
not literally state the Lie result, and no such literal prior statement was
located in the bounded search. Nevertheless, this presents a serious
routine-adaptation objection under the user's standard. The smaller generic
dimension is not nominated as a separate result.

## What was verified

`python scripts/check_exact.py` passed, using only integer/rational arithmetic:
all 8000 basis Jacobi identities for the rational example, class exactly two,
derived dimension 14, defining relation of skew rank six, and 1120 coordinate
comparisons for the generic change-of-basis formula.

`python scripts/run_lean.py` passed with the required Lean 4.34.1 binary,
mathlib HEAD and manifest both verified at
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Six declarations in
`formal/ParameterObstruction.lean` were compiled into fresh lane-local objects
and audited. Their dependencies use only `propext`, `Classical.choice`, and
`Quot.sound`. There are no admissions or forbidden evaluation shortcuts.

**The Lean result is partial.** It certifies the polynomial chart obstruction,
not the literal Lie-algebra conjecture. Missing formal bridges: existence of
the independent real coefficients; Lie-algebra construction and class;
derived-space dimension; adaptation of an arbitrary multiplicative basis;
and derivation of the chart from that basis. The explicit rational example's
universal rank/basis argument is ordinary mathematics only. No full paper or
extracted source-theorem replay is claimed. No independent agent review was
performed, in accordance with the solo instruction.

## Other leads and exclusions

| Target | Disposition |
|---|---|
| 347481, inverse Vandermonde diagonal maximum | Old lane already rejected it as a classical positive-definite-matrix consequence; reread source, did not recount. |
| 372787, Johnson Toeplitz identity | Actual source arXiv:2601.18977 proves its Conjecture 1.2 in Section 2. Stale database label. |
| 372585, symmetric hyperbolic polynomial inequality | Actual source arXiv:2601.10602 proves it as Theorem 2.12. Stale database label. |
| 352819, older Le hyperbolic inequality | Same mathematical family; newer source settles the symmetric-matrix assertion. Garbled database text not treated as a new target. |
| 372716, Heib–Bruschi kernel criterion | V1 Conjecture 82 is withdrawn in v2; v1 already supplies the relevant direct-sum example. Excluded. |
| 362175, weighted commutator bounds | Read source arXiv:2403.04199. Later rank-one results do not settle the general problem. No complete general proof or counterexample found; no claim. |
| 343202, inverse eigenvector products | Preliminary screen only. Tied to real polarization; no complete proof, no novelty clearance. |
| 377365, primitive powers of integer matrices | Preliminary screen only. No complete proof, no novelty clearance. |

The initial exclusions were respected: first-batch families, active Banica–Nechita
332493, Zhou 367221, FZZ 368343, Ku/Johnson1981, public Tang–Zhang 371031
and Lin 332939 refutations. Old lane notes were read before target selection.

## Prior-art scope and limits

Actual theorem bodies examined include Calderon Martin's multiplicative-basis
decomposition results; the corresponding arbitrary-algebra decomposition in
Navarro's thesis; Milentyeva's generic class-two parametrization and Theorems
1–3; Gorbatsevich's nice/beautiful-basis Theorems 1–4; and the definition,
structural lemma and graph-algebra discussion of Dere–Gantois. Nice bases
impose an extra condition, so their nonexistence alone does not prove the
needed nonexistence of multiplicative bases.

Live semantic GitHub search found public Heib–Bruschi v1 Conjectures 80 and
83 refutations in `the-omega-institute/trureturing`; their full problem notes
were fetched at the exact commit returned by search and read. These are
neighboring, different conjectures, already excluded. Earlier cached trees
missed these hits; the final provenance does not rely on those negative hits.
The live recursive trureturing tree is truncated and is not exhaustive.
The live formal-conjectures tree is untruncated with no relevant path hit.
Searches for the target number and relevant wording did not locate a literal
Conjecture 91(a) settlement; this is bounded non-detection, not novelty proof.

MathDB 372720's three additional alleged source papers were retrieved and
checked: their subject matter is unrelated; they are not supporting sources.
No MathDB-specific connector was available; records were obtained via the
public read-only API. The MSE answer was readable through the web extraction
tool; a direct HTTP download returned 403 and was not bypassed. The failure
receipt is retained and must not be mistaken for a hash of the answer.

`provenance.json` and the receipts under `sources/` give URLs and hashes;
`verification/result.json` and `verification/exact-result.json` give check
results. All writes stayed in this lane. No git commands, children, posts,
account changes, uploads, or messages to other people were used.
