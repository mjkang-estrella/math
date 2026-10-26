# Active campaign checkpoint

Goal: 20 **distinct** MathDB problems with an exact claimed outcome fully
certified in Lean, a written paper, independent review and reproducibility.
This is a new strict count; do not equate the earlier 19 publications with
19 fully formalized main theorems. The historical audit in the matrix lane
finds 0/19 have that stronger coverage. Do not split one problem's lemmas,
normalizations or dimensions into separate outcomes.

Latest status: **4/20 verified**. The first three new candidates below have
now passed independent review, paper QA, full archive hash checks, and
isolated-source replay. The authoritative current count is `ledger.json`.
Earlier pending-status paragraphs below are chronological implementation
notes and are superseded by this status.

Active work now: discrete/algebra discovery remains in functions cell 58;
new Fibonacci orbit-weight implementation is in functions cell 102. Its
assigned output is `../fibonacci-weight-lane`, MathDB371201. The review in
cell 85 completed PASS for all three candidates and is saved as
`reviews/first-three.md`. No delegate cancellation is needed for completed
tasks. If a waiting call returns a `next` instruction, obey it.

Verified ledger currently contains MathDB336488 only. Its complete paper,
Lean proof and release are in `../premagic-diagonalizability`, commit
`e99b1337ab`.

Parent candidate MathDB336487 is in `outcomes/norm-one`: full Lean main
counterexample compiles and generic verifier reports 14 declarations with
only standard axioms. The two-page paper is drafted and has had visual QA;
a small comma typo was fixed and requires final rerender. Independent review
and final package are still required before counting it. This is explicitly
an elementary normalization correction, not a major research breakthrough.

Three parallel ultrafast discovery delegates own neighboring directories:

- `../twenty-proof-matrix-lane` (also holds historical audit)
- `../twenty-proof-discrete-lane`
- `../twenty-proof-algebra-lane`

Do not edit their live files. Their briefs request exact primary sources,
distinct questions, and compiled full Lean proofs rather than only searches.
The active delegated calls are being awaited in functions cell 58. Follow
their returned next instructions, never poll task_status or use watchers.

Update: the matrix lane has completed two compiled full proofs, for
MathDB362146 (permutation-like eigenvalues) and MathDB340783 (fair-discrepancy
propagation counterexample, crediting Patel's posted construction). Parent
has copied the exact Lean files into canonical `outcomes/permutation-spectrum`
and `outcomes/fair-discrepancy`, independently rebuilt them with the generic
verifier, and built/visually inspected two-page manuscripts. They remain
uncounted pending independent review.

A new explicit ultrafast review delegate is reviewing all three candidates
(norm-one, permutation-spectrum, fair-discrepancy), with output restricted to
`reviews/first-three.md`. Its running tool call is functions cell 85. The
other two discovery lanes remain in functions cell 58. The matrix task has
already returned a completed result through that cell; do not treat it as
still working. Follow subsequent returned `next` instructions.

The canonical matrix paper TeX differs from lane originals only in layout:
long identifiers/hashes on their own lines and shorter equivalent MathDB
URLs. No mathematical prose was changed. The reviewer is hashing the lane
originals, so record the parent-verified layout-only adoption when sealing
the canonical copies.

`verify_outcome.py` is a new campaign-level verifier for single-module
outcomes with `outcome.json`, using `pins.json`. It compiles a byte-identical
copy in `build/` and prints types/axioms for every local declaration.
Review this infrastructure along with the first parent candidate before
relying on it for acceptance.

The user wants work to continue until the goal is actually achieved. Do not
mark the goal complete because of elapsed time, an arbitrary research round,
or partial candidate progress. Failed candidates and existing posted proof
attempts must be labeled honestly; worldwide novelty is not established by
a missing MathDB solution. The current task does not authorize new external
publications or messages.

Useful queued candidates, not yet assigned or counted:

- MathDB371201: weight preservation for Fibonacci recurrences. Source
  arXiv:2510.24882v2, Conjecture17. There is an existing posted orbit-fiber
  proof by Shivam Patel; credit it if formalizing. A full certificate should
  define actual Fibonacci/chiral permutations on `(ZMod m)^2`, the reduction
  map for `d|m`, its uniform fiber sizes, and orbit partition weights. Merely
  assuming the orbit/fiber identities would be partial coverage.
- MathDB371202: proposed distribution of Fibonacci minima. Same primary
  paper, Conjecture20. Existing posted refutation gives limit `5/24` for
  square-uniform initializations, not `1/4`. Need full counting/limit link if
  formalizing, not just arithmetic `5/24 != 1/4`.

Full captured statements and existing posted attempts are in
`queued-sources/`; no priority claims should be based on re-proving them.
