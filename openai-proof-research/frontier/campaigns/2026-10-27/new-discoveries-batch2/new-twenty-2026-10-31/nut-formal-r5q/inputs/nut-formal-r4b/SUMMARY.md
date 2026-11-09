# MathDB 365943 r4b: partial B2 progress, zero credit

`finite_obstruction : Nut8.FiniteObstruction` remains absent. The assignment's
main goal is not achieved, and no unconditional target or acceptance is claimed.
Counts stay at 20/40 beyond the previous 39. Part A/r4a was not touched.

Three new proof modules advance the first remaining item, B2:

- `SupportGraph.lean` extracts the connected simple off-diagonal support on
  `Fin 8` from every structural matrix and proves degree at most three.
- `GraphDeletion.lean` uses mathlib's spanning-tree-leaf removable-vertex result,
  transports deletion to the smaller standard finite type with an actual graph
  isomorphism, and preserves connectedness and the degree bound.
- `CheckedGraphIso.lean` converts checked permutation lists to actual finite
  permutations and successful adjacency checks to graph isomorphisms. It also
  composes the inherited extension closure soundness with this conversion.

These are proved bridges, not a universal graph coverage theorem. Still missing
are the row-major graph encoding proof, the transported eligible neighbor mask,
and the induction connecting arbitrary connected subcubic graphs to L_8.
Consequently B4 parent data, B3 augmentation completeness, the remaining 9,140
of 9,172 certificate records, and B6 composition remain unfinished. The inherited
32-case certificate batch and pilots are unchanged. See GAPS.md for exact
obligations and statement-correspondence.md for theorem scopes.

All 84 supplied input files are copied with matching SHA-256 hashes and verified
unchanged afterward. The mandated r3b archive hash is verified. The apparent
64-module input count is 64 files: 56 Lean source files and eight oleans. All 56
inherited Lean sources, including FiniteGrammar, Nut and VerifiedDet, are
byte-identical; inherited binary copies are kept under inputs and excluded from
the source-only replay packet. No inherited code or interface was repaired.

Validation metrics are recorded in results.json and replay receipts. The fresh
extracted replay is a check of this partial packet only. AuditR4 prints all local
declarations, including generated ones, with full type/body/flags/transitive
axioms. Logs of failed and successful development calls have unique filenames;
none was overwritten in this lane. Six false Lean controls and existing-olean
refusal are recorded. Portable replay instructions are in REPRODUCE.md.

The lane contains no child-agent work, git operations, shared ledger edits,
other-lane writes, external messages, network requests, browser tabs, publication
or uploads. No novelty clearance is claimed. No background jobs are left at
handback. Root alone decides acceptance; this lane remains incomplete and
uncredited.

Fresh replay passed all 60 strict compilations and 60 separate leanchecker calls.
The final audit covered 691 local declarations, including 36 new generated or
explicit declarations. All six false Lean controls were rejected. The 126 capped
calls used 695.25 summed wall seconds; peak sampled private
memory was 2,477,232,128 bytes. No cap was violated.

Validation correction: the initial new permutation-lookup negative control lacked
an explicit finite dimension and also produced elaboration errors. Its complete
log is retained. The corrected control specifies `(n := 2)` and was rerun under
the same watchdog; it is rejected solely with the intended unsolved `False` goal.
The portable driver includes that one-line correction. All formal theorem sources
and compilation commands are byte-identical to the strict fresh extraction; the
corrected control was validated separately without repeating unchanged builds.
The main replay has 126 receipts and the supplementary corrected control has one.
