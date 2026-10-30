# Version 2 change report

Manuscript: **The Read-Once Factorial-Divisibility Conjecture: Algebraic Proofs Through Six Inputs**

Version 2 DOI: **10.5281/zenodo.21853500**

Comparison baseline: the uploaded Version 1 source package
`Read_Once_Factorial_Divisibility_Zenodo_DOI_source(1).zip`.

This report records substantive changes in Version 2.  The main conjecture,
the theorem proving the factorial target through six inputs, and the original
future-work scope are retained.  Version 2 is a correction and strengthening
of the same manuscript, not a replacement by a different exact-classification
paper.

## 1. Proof corrections and clarifications

- Repaired the four-input universal `36` proof.  The no-3-multiple branch is
  now split by parity and the former unsupported same-parity/mod-12 step is
  replaced by explicit congruence constructions.
- Strengthened the sign-normalization lemma to a full sign-transport statement
  for arbitrary read-once expression trees using `+`, `-`, and multiplication.
  The proof is by structural induction and leaves only an irrelevant overall
  sign at the root.
- Tightened the signed-class triangle lemma by stating the conditions under
  which the admissible sign is unique.
- Expanded several three-input arguments so that the unused third leaf is
  explicitly incorporated in collision branches; this removes ambiguity about
  the read-once "use every input exactly once" requirement.
- Rewrote the three-input `10` construction to make the parity branches and
  legal use of the third leaf explicit.
- Expanded the same-parity `7 -> 14` explanation so the additional factor `2`
  is explicit in every branch.
- Rewrote the `2O2E -> 40` sign-compatibility argument without inverse/ratio or
  square notation; the proof now uses direct signed congruences and parity.
- Rephrased the delicate D2 branch of the `3O1E -> 60` proof so the sign-product
  contradiction is expressed directly, without power notation.
- Corrected/clarified terminology in the small signed-class lemma: it is now
  stated for a finite abelian group `G` with `|G| <= 6` and the proof explicitly
  switches to additive notation.
- Clarified ordered representatives in the `P(4;26)` residual table and minor
  variable naming in the `P(4;22)` proof.
- Clarified the modulo-3 finite sign classification in the `P(4;33)` proof so
  it cannot be mistaken for enumeration of integer inputs.

## 2. Additional four-input universal constructions

Version 2 adds complete algebraic/congruence proofs of the following further
universal four-input guarantees:

`P(4;m)` for

`m = 17, 19, 21, 22, 23, 25, 26, 27, 28, 30, 32, 33, 35, 40`.

These are presented as additional proved guarantees.  The manuscript does not
claim that the displayed collection is an optimal or exact classification.
The later four-input refinements are not propagated into a recomputed
five-input or six-input source-pool closure.

Notable proof devices added in this appendix include signed-class group
relations, finite residual signed-class classifications, and complementary
binary lift arguments for the `32` and `40` constructions.

## 3. Residual tables: interpretation and reproducibility

- The residual tables for the `17/19`, `23`, and `35` arguments now state
  explicitly that their rows are **signed residue-class configurations**, not
  sampled or enumerated integer input quadruples.
- A row such as `(1,2,3,4)` modulo `17` therefore means that, after sign
  normalization and relabelling, the four inputs lie in those signed residue
  classes; it does not mean that the original inputs are literally
  `1,2,3,4`.
- The source package includes `verify_residual_tables.py`.  The script
  independently reconstructs the finite residual lists for the `17/19`, `23`,
  and `35` arguments and checks that every displayed certificate is a legal
  four-leaf read-once `+,-,*` expression vanishing modulo the target.
- The script is a consistency check only.  The manuscript's proofs are
  self-contained and do not rely on computation.

## 4. Parity-pattern summary through six inputs

- Added a compact appendix table covering every odd/even pattern for
  `n = 1,...,6`.
- The table points readers to the corresponding algebraic/congruence proof of
  the factorial target.
- For `n=5`, the universal `120 = 5!` argument covers all six parity patterns
  at once.
- For `n=6`, the seven parity patterns remain covered by the original
  case-by-case algebraic/congruence proof of `720 = 6!`.
- This summary is organizational; it does not introduce a new exhaustive
  parity-frontier or closure computation for `n=5` or `n=6`.

## 5. Frontier/provenance wording

- The frontier discussion is clarified as a record of the displayed proved
  source pools and their divisibility-dominance deletions.
- The existing warning is preserved that incomparable guarantees may come from
  different expressions and therefore cannot be combined by taking an lcm.
- The paper continues to make no optimality claim for these recorded
  frontiers.

## 6. Disclosure and source-package updates

- Updated the generative-AI disclosure to identify OpenAI ChatGPT (GPT-5.6),
  describe its exploratory/editorial role, and state that the author reviewed
  and assumes responsibility for all mathematical content.
- Updated the data/code availability statement to mention the supplementary
  residual-table consistency script while explicitly stating that the
  algebraic proofs are self-contained.
- Added this Version 2 change report and the residual-table verification script
  to the source package.

## 7. Items intentionally unchanged in scope

- The manuscript title and central conjecture are unchanged.
- The abstract retains the Version 1 framing.
- The main theorem remains the proof of factorial divisibility through six
  inputs.
- The `n=5` factorial target remains `120` and the `n=6` target remains `720`;
  Version 2 does not attempt a new complete closure or optimality analysis at
  those input sizes.
- The conclusion/future-work direction remains the original one: the general
  conjecture is open beyond the proved range.
