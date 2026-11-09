# r10 SUMMARY — BunUpperSupport strict execution (Pi GLM5.3Flash)

## Status: STRICT COMPILE SUCCESS, SEALED, AUDITED, CHECKED

MathDB 382297 auxiliary upper-support theorem. Credit 0; campaign 52/60 unchanged.

## Execution sequence (as mandated)

1. `verify_frozen.py before` → `{"count": 594, "mismatches": []}` (1794004059.3).
2. FIRST mathematical operation: `check.sh BunUpperSupport` on the root-repaired
   copy, no prior inspection/planning/rebuild. **EXIT 0** on the first compile.
   - Receipt: `receipt/1794004062762172392_lean_BunUpperSupport.json` (exit 0,
     true reaped exit, no tail masking, all caps recorded, wall 1058 ms,
     peak group RSS sampled 1.77 GiB, affinity [0,1], MALLOC_ARENA_MAX=2).
3. Sealed `receipt/SEALED_BunUpperSupport.json` with source/log/olean hashes.
4. Scoped `#print axioms` audit under the same runner/caps
   (`receipt/1794004160223685655_axioms_UpperSupport.json`, EXIT 0):
   - `Bun.startST_parts_range`: [propext, Classical.choice, Quot.sound]
   - `Bun.stf_parts_range`:    [propext, Classical.choice, Quot.sound]
   - `Bun.stf_upper_support`:  [propext, Classical.choice, Quot.sound]
   Only the three allowed axioms; no sorry/admit/new axioms/unsafe/native_decide.
5. `leanchecker BunUpperSupport` under the same runner with pinned toolchain bin
   prepended to PATH (`receipt/1794004185658675669_leanchecker_UpperSupport.json`,
   EXIT 0). A first path-argument invocation failed on module resolution; its log
   `logs/1794004170789406682_leanchecker_UpperSupport.log` is retained, not
   counted as a pass. The passing run invoked by module name with full LEAN_PATH.
6. Post-checker hash reverification (explicitly required even for module-name
   invocation), identical to sealed values:
   - src/BunUpperSupport.lean sha256 `367e352d192210719de0a376eafeac19605cec37b0eda24541811676963e335c`
   - build/BunUpperSupport.olean sha256 `80e682258236ef6b07a6bfd7f66715ba98712ab97b7d5c0c5f57794150386b3f`
7. `verify_frozen.py after` → `{"count": 594, "mismatches": []}` (1794004199.0).
   All 594 frozen inputs preserved.

## Scope honesty

ONE theorem delivered: `Bun.stf_upper_support` (∀ n u j k, ∀ w : Asg n j,
∀ sigma : Bool, k ∈ sval sigma (stf n u j w) → k ≤ j), plus its in-module
supporting lemmas `Bun.startST_parts_range` and `Bun.stf_parts_range`, exactly
as present in the repaired source. `stf`, `sval`, semantics untouched; the
conclusion is proved, not assumed. No lower support, stability, new-index
indicators, Reach bridge, counting, token fibers, reflection, terminal payoff,
cardinality endpoint, negative controls, fresh extracted all-source replay,
independent audits, or paper in this task.

## Development-import scope (per TASK)

check.sh imports the 7 verified production baseline builds (r7/r5/r2/r1 + own
build) and pinned mathlib d13f23b7…; the failed r9 build is not imported. This
is development import reuse, NOT a fresh all-source extracted replay.

## Unpaid remainder (exact, for the ledger)

- Full lower-support counterpart and stability properties
- New-index indicator lemmas beyond stf_parts_range consequences
- Literal Reach bridge / reachability characterization
- Token-fiber and reflection lemmas
- Terminal payoff and cardinality endpoint (MathDB 382297 main statement)
- Full independent adversarial audits; negative controls
- Fresh extracted all-source replay (no development imports)
- Review, paper, acceptance, credit (credit stays 0; 52/60 unchanged)
