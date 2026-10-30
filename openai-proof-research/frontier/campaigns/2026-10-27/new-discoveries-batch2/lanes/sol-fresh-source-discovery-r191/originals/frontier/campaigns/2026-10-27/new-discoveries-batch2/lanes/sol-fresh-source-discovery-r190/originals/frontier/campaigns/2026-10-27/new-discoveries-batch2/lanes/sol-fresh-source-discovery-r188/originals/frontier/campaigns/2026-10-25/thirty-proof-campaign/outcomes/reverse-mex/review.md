# Independent review: MathDB374728 reverse-mex counterexample

Verdict: PASS, complete nonvacuous counterexample to the actual source Conjecture1 for ordinary subtraction Nim. Only the base set S={3,6,10} is claimed; not its separate additive-set conjecture, pass-game claims, or the posted infinite-scaling strengthening.

Reviewer: parent integrator, independent of the agent who authored this mathematical/formal development. Read the complete formal source and written argument, actual primary Definitions4,8,12–13 and Section4.1 Conjecture1, including the generic ordered three-element subtraction-set setup, and the existing Patel solution. A fresh isolated pinned compilation of the parent copy passed all45 declarations with warnings treated as errors; only propext, Classical.choice and Quot.sound are used transitively.

Exact accepted sources:
- formal/ReverseMex.lean SHA256 `e77c3351ce2162bf96090e16ae8c5c46e7e98033bf6e751cc31ffe503ef33449`
- main.tex SHA256 `4197af28894428ad5252e92603a4b499a2f8f39ade5b1b0a5780c37f4b414207`

## Exact source bridges

The source legal move set is the filtered finite subtraction set followed by the predecessor-value image. moves_source_bridge proves its equivalence with the guarded three-move recurrence, rather than assuming an unguarded formula at small heaps. The witness sequence has the exact twelve-term prefix and absolute-residue tail table. Its mex equation is checked for every heap below22 and for all13 residue classes thereafter, when every predecessor is in the tail. Strong induction proves uniqueness for every sequence satisfying the actual source recurrence. Thus this is an all-heap Grundy certificate, not extrapolation from finite data. P_outcome_recurrence also proves the normal-play losing-position recursion locally, so P=Grundy-zero is connected to the source game outcome.

The source period condition holds with p13,q11 for every heap at least12. Definition12 leaves integer targets at least12 unchanged and lifts lower targets by a positive integer multiple of13 into[12,24]. reduce_spec proves precisely both branches, including negative targets and the positive lift. It does not silently apply an ordinary zero-based modulus to prefix positions.

The source distance uses positive natural steps (consistent with its Definition12 positive subtrahend convention and separate nonnegative heap convention). Hit explicitly requires k≥1. Nat.find has a proved witness for every heap, and dist_eq_iff checks both the first hit and absence of every smaller positive hit. The thirteen-case table is valid for every w, including the prefix. The full P classification includes heaps0,1,2,9 before the tail; no initial exceptions are omitted. The qualifying P positions of even distance at least4 are exactly0 and positive multiples of13, with distance4. The final theorem includes a positive witness13, so nonvacuity does not depend on whether one informally focuses on positive rather than nonnegative heaps.

For every qualifying heap, actual source-reduced targets w+10-3 and w+10-9 have Grundy values2 and0. Hence the whole universal condition(a) is proved, not just a selected witness. The inverse implication nevertheless fails: heap5 has Grundy1 while the mex of follower values2,3,2 at8,11,15 is0. The counterexample proves all source numerical ordering and admissibility hypotheses. No probabilistic or numerical limiting argument is involved.

## Written argument, prior credit and production

Independently checked all three rows of predecessor values in the paper's tail table, all distance minima, both source-reduction branches, and the final arithmetic. The source statement is ordinary subtraction Nim despite the larger manuscript's pass-game title; Section4.2's separate pass assertions are expressly excluded. The final paper matches the complete certificate.

The original MathDB reply is by Shivam Patel, solution UUID93319111-a98e-4c7c-a497-fc6dd230eb22. Its content hash and primary snapshots are inventoried in source.json. Prior credit and the lack of any discovery/first-formalization claim are prominent. Pi discovery work identified this existing candidate for the project; the mathematical credit remains Patel's.

Parent production changes affected author/license, spacing, source-package wording and page margins only. All3 final rendered PDF pages were individually inspected; tables and formulas are legible and there is no overflow, clipping or unresolved reference. The proof source is byte-identical to the author's. This counts one distinct source-question outcome; table entries and supporting bridges add no extra count.
