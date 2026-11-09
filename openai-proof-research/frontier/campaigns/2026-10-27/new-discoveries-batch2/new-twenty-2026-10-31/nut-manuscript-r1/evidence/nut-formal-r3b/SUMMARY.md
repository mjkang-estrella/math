# MathDB 365943 r3b: incomplete Part B, zero credit

The required theorem `finite_obstruction : Nut8.FiniteObstruction` was not
proved. No unconditional endpoint exists and this packet does not meet the
assignment's acceptance gate. No result is self-accepted and counts are unchanged.
GAPS.md lists the precise remaining obligations.

Implemented and strictly replayed:

- B1: permutation invariance of Admissible; cofactor relabelling; sign-free
  structural switching invariance; determinant and principal-cofactor switching
  invariance in arbitrary dimension; refutation transport.
- B2 finite data: lists of sizes 1, 1, 2, 6, 10, 29, 64, 194, with 1,722 explicit
  extension isomorphism certificates, including 1,158 at the final step. Every
  eligible neighbor mask for every listed source is kernel checked against
  explicit target and permutation data. Generic checker soundness is proved.
  The universal connected-graph induction is still absent.
- B4 algebra: a well-founded parent-tree sign construction, sign values and
  normalization of parent-edge signs and weights. Connected-graph extraction
  of such parent data remains absent.
- B5: the first 32 r2 matrix certificate records, using the byte-identical
  sparseDet correctness theorems. The remaining 9,140 records are not checked.
  The trial took 25.92 seconds and 2.44 GB sampled private memory; extrapolation
  to a full run is only a planning estimate. B3 and B6 remain unimplemented.

Fresh source-only extraction `fresh-extracted` passed strict sanitized rebuild,
separate leanchecker for all 55 scheduled modules, and all-declaration audit of
655 local declarations including generated declarations. The audit prints
module, full type, opaque-inclusive body, unsafe/partial/axiom flags and
transitive axioms. Only propext, Classical.choice and Quot.sound occur. Five
Lean negative controls were rejected and the existing-olean refusal control
passed. All 115 replay calls stayed within caps; summed process wall
time was 442.74 seconds and peak sampled private memory was 2,451,771,392 bytes.
Full audit: fresh-extracted/logs/strict-AuditR3.log. Receipts:
fresh-extracted/logs/replay.json.

All 32 assigned files were hash-bound before/after and copied with hash identity,
including the required r2 archive hash. One auxiliary canonical-refinement script
was copied and bound when adapted; auxiliary-input.json distinguishes it from
the initial manifest. All inherited Lean files, including Nut, FiniteGrammar
and VerifiedDet, remain byte-identical. Only new modules were added. Failed
local development trials reused log filenames, so some earlier logs were
overwritten; this full-log requirement deviation is recorded in
logs/development-history.md. The final extracted replay logs are complete.

No child agents, git commands, other-lane writes, shared ledger edits, network
requests, browser tabs, external messages or publication were used. No background
jobs remain at handback. No prior-art gate was repeated and no novelty clearance
is claimed. Source-only packet: nut-r3b-source.zip; replay: REPRODUCE.md;
statement mapping: statement-correspondence.md. Root alone adjudicates acceptance.
