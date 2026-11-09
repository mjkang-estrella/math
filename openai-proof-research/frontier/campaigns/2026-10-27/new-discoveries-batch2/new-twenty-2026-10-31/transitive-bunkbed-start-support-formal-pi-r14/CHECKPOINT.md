# CHECKPOINT — transitive-bunkbed-start-support-formal-pi-r14 (sealed)

State: SEALED, no further mathematical work in this lane.

## What exists (actual, on disk)
- `src/BunStartSupport.lean` — sole new source. One theorem `Bun.startST_support`:
  for all `n j k : Nat`, all `w : Asg n j` and `sigma : Bool`,
  `k in sval sigma (startST n j w) -> k = j`.
  Uses the EXISTING `startST`/`sval`/`Asg` from `BunState` unmodified; no
  redefinition, no extra hypotheses, no recursive stf/Reach/probabilities/counts.
  Covers `n = 0`, `j >= n`, both layers and both vertical-bit outcomes via the
  actual `dite`/`ite` structure of `startST`.
- `build/BunStartSupport.olean` — compiled by pinned lean 4.34.1, runner caps
  cpu120/wall140/devguard130/AS12GiB/RSS6GiB/MALLOC_ARENA_MAX=2/<=2CPU, exit 0.
- `audit/BunStartSupportAx.lean` — scoped `#print axioms` audit.
- Receipts: build `receipt/1794011809072540936_lean_BunStartSupport.json` (exit 0);
  kernel checker `receipt/1794011815767791160_leanchecker_BunStartSupport.json` (exit 0);
  axiom audit `receipt/1794011884638815943_audit_bunstart_support_axioms.json` (exit 0).
  Three earlier failed build receipts preserved as honest attempts
  (1794011617721656616, 1794011677319061257, 1794011789895620580; diagnostic-driven edits only).

## Hashes (source/olean/logs/receipts; all full 64-hex sha256)
- source sha256 c99ead1ea5d55cb194cb7e0b124afb89c36f92dc3e33dde6c9fae0ad8401c9d2
- olean  sha256 317e7ae93d5070d6ff1af5e7bf3057d9827e4b3e3e0ac0cb8fba3a092c51fc8b
- build log sha256 911a8140d383afd707021b7fe09aefc7e44c42da7fdb71bf9ccf1b83f500a5a2
- checker log sha256 a93faf23ce06b9c7fd92d4ed60e2a1bb05aee5bfa74a318a26ff9c676be19deb
- audit log sha256 31830189242a0ca07225af080745946847346b9a831f6a8d590cb3bc81ac17bf
- build receipt sha256 9caffe4d358c8c6a334c31e0e4dad10f09fbaa9ead12a48795c6f201f6a03999
- checker receipt sha256 b38ffb0ce8d999c3b3bdaebb06b256b63cd7b4e25914dea9579c1c5ed0abfef1
- audit receipt sha256 933a2114c3b72bac6c6d7725c329b22f991af17309526fdcb36f4f289791b90e
- Post-checker source/olean hashes IDENTICAL to the build receipt (stability verified).

## Audit result (verbatim from log)
'Bun.startST_support' depends on axioms: [propext, Classical.choice, Quot.sound]
No sorry/admit/new axioms/unsafe/partial/native_decide/extern/implementedBy anywhere.

## Frozen inputs
717/717 verified before math (`frozen-before.json`, zero mismatches); after-check
recorded in `frozen-after.json`. Bootstrap receipt preserved untouched.

## Credit / scope (honest)
- MathDB 382297 credit: 0. Campaign: 52/60 beyond 39 prior, unchanged.
- PAID by this lane: the single start-state support fact only.
- UNPAID (explicitly, not started here): full recursive `stf` support, stability,
  new indicators, literal Reach bridge, fresh-token fibers, reflection,
  terminal payoff/cardinality, deep audit/negative controls, extracted replay,
  independent review, paper, acceptance.
- Active crown r21 and discovery corpus r367 lanes: untouched
  (no reads/hashes/globs/polls this session beyond the TASK-mandated
  LEAN_PATH build dirs, which are read-only imports).
