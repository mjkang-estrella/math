# CHECKPOINT — transitive-bunkbed-update-lower-formal-pi-r12 (sealed)

State: SEALED, no further mathematical work in this lane.

## What exists (actual, on disk)
- `src/BunStepLower.lean` — sole new source. One lemma `Bun.stepU_lower_closed`:
  for all `m u k : Nat`, `R S : Finset Nat`, `x y z sigma : Bool`,
  `(∀ a ∈ R, u ≤ a) → (∀ a ∈ S, u ≤ a) → u ≤ m → k ∈ sval sigma (stepU m R S x y z) → u ≤ k`.
  Uses the EXISTING `ind`/`stepU`/`sval` from `BunState` unmodified; no redefinition,
  no selected-conclusion assumption, no recursive stf_lower_support/Reach/counting.
- `build/BunStepLower.olean` — compiled by pinned lean 4.34.1
  (commit 5045d0056413266e57c625dcd7c365b10e377c52), runner caps
  cpu120/wall140/devguard130/AS12GiB/RSS6GiB/MALLOC_ARENA_MAX=2/<=2CPU, exit 0.
- `audit/BunStepLowerAx.lean` — scoped `#print axioms` audit.
- Receipts: build `receipt/1794008524687485694_lean_BunStepLower.json` (exit 0);
  audit `receipt/1794008635916000062_...` (exit 0);
  kernel checker `receipt/1794008668703256235_checker_bunsteplower_mod.json` (exit 0).
  Two earlier failed checker invocation receipts (path-form and PATH-less) are
  preserved as honest attempts: `..._checker_bunsteplower.json` (exit 1, no lean on PATH),
  `..._checker_bunsteplower_path.json` (exit 1, path not resolvable; module-form succeeded).

## Hashes (source/olean/log; re-verified identical after kernel checker)
- source sha256 54a3573910df26b0e30c3aee458e5a505fc7a1e3acc068ff58bc75c31a975934
- olean  sha256 a2d7ee4c34f5297e655af0aa67c69227a68877fcb01c19c9ec6ceeb1c3b520d4
- build log sha256 abe0c3280bf76b64d6262987d674f9c27c8fb2fff721e735c336b8b76615dbdd

## Audit result (verbatim from log)
'Bun.stepU_lower_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
No sorry/admit/new axioms/unsafe/native_decide anywhere.

## Frozen inputs
657/657 verified before math and 657/657 after work; zero mismatches
(`frozen-before.json`, `frozen-after.json`). Bootstrap receipt preserved untouched.

## Credit / scope (honest)
- MathDB 382297 credit: 0. Campaign: 52/60 beyond 39 prior, unchanged.
- PAID by this lane: the single update-lower closure helper only.
- UNPAID (explicitly, not started here): full recursive `stf_lower_support`,
  stability, new indicators, literal Reach, token fibers, reflection,
  terminal payoff, cardinality endpoint, all broader audits, negative controls,
  fresh extracted all-source replay, independent reviews, paper, acceptance.
- Active crown rank-one-map r19 and Sol crown-component-quotient lane: untouched
  (no reads/hashes/globs/polls of other lanes this session beyond the
  TASK-mandated LEAN_PATH build dirs, which are read-only imports).
