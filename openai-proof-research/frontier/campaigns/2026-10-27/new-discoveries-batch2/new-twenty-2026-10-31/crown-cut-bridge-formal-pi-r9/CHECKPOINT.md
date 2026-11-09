# r9 CHECKPOINT — 2026-11-06 (updated after first compile)

MathDB 369163. Credit 0; campaign 52/60 beyond 39 prior. Acceptance is root-only.

## Compiled milestone (real, receipted)

`src/CrownVCutBridge.lean` STRICT-COMPILED under the supplied `check.sh`
(lean 4.34.1, `-DwarningAsError=true`, `-j1 -M3500`, runner caps: cpu120s /
wall140s / devguard130s / AS12GiB / RSS-guard6GiB / MALLOC_ARENA_MAX=2 /
2 cores). Exit 0, wall 1354 ms, no warnings.

- source sha256 `227e497d0b0848cf7937f21988b85b9e9b1e7eeafdfb6e21f74a710e5f67a4ca`
- olean sha256 `ff83dfb60ea9e0026020f433cc9aec6745a878c0faa2f3c3aab3922c6c498d16`
- build receipt `receipt/1793975760584031819_lean_CrownVCutBridge.json`
  (exit 0; log sha256 `bfecc69fe54d85c6998e35b27479b493369ec97a828771bded017957be99d356`)

Declarations, all kernel-checked, no sorry/admit/new axioms:

1. `CrownV.bridge_cadj_symm` — symmetry of `cadj` (no axioms).
2. `CrownV.cadj_left` / `CrownV.cadj_right` — index rewriting along equations.
3. `CrownV.sameC_of_clique` — rerouting: if all pairs of `D`-neighbors of `t`
   are `D`-connected, every `SameC (insert t D)` path between `D`-points is a
   `SameC D` path. Induction invariant: endpoint in `D` with `D`-connection to
   the start, or endpoint `= t` reached from a `D`-neighbor `D`-connected to
   the start; the clique hypothesis closes the leave-`t` step.
4. `CrownV.vcut_witness` — for `t ∉ D`:
   `VCut D t ↔ ∃ b c, b ∈ D ∧ c ∈ D ∧ cadj t b ∧ cadj t c ∧ ¬SameC D b c`.
   Forward: by_contra; the negated witness is literally the clique
   hypothesis, then `sameC_of_clique`. Backward: `b -> t -> c` in
   `insert t D`.

Axiom audit (probe `probe-axioms.lean`, runner receipt
`receipt/1793975845487407253_probe_axioms2.json`, exit 0):
`sameC_of_clique`, `vcut_witness` depend exactly on
`[propext, Classical.choice, Quot.sound]`; `bridge_cadj_symm` on none.
One earlier failed probe kept for honesty:
`receipt/1793975825134605536_probe_axioms.json` (exit 1, LEAN_PATH not
exported; log kept).

Baseline: seven modules reused hash-identically, imported READONLY from
completed r7 build via LEAN_PATH; nothing rebuilt. r8 never touched.

## Frozen verification

`verify_frozen.py before`: 547/547 matched, no mismatches
(`frozen-before.json`). `verify_frozen.py after`: see frozen-after.json.

## Still unpaid (accurate)

- valid family -> `Cutset` (case module): not started.
- converse `Cutset` -> valid family: not started.
- actualJ/Pc decomposition; all-field homogeneous degree0..3 exclusions
  incl. char2; quartic exact-colon witnesses; literal VIs4: not started.
- local-v=4 algebra endpoint, full certificate/audit, extracted strict
  replay without r7 path, independent review, paper: not started.

No processes left running; runner reaped children (see receipts
`leader_reaped`/`group_members_left`).
