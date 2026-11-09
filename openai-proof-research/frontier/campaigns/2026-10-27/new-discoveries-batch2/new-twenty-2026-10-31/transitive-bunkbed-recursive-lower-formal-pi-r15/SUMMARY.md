# r15 SUMMARY — BunLowerSupport strict execution (Pi GLM5.3Flash)

## Status: STRICT COMPILE SUCCESS, SEALED, AUDITED, CHECKED

MathDB 382297 auxiliary lower-support module. Credit 0; campaign 52/60 unchanged.

## Execution sequence (as mandated)
1. `bootstrap.py` then `verify_frozen.py before` -> {"count": 759, "mismatches": []} (1794012197.6); 759 frozen inputs preserved throughout.
2. FIRST mathematical operation: WROTE src/BunLowerSupport.lean, then `check.sh BunLowerSupport` — no preceding source/convention/API inspection, probes, baseline rebuild or long planning.
   - First compile EXIT 1 with exactly two diagnostics (line 66/86: hP.left/hP.right expect the element explicitly); single targeted edit (hP.1 k hk / hP.2 k hk); prompt recompile EXIT 0.
   - Failed receipt retained: receipt/1794013198745389724_... + log (never rerun unchanged).
   - Success receipt: receipt/1794013212058888424_lean_BunLowerSupport.json (true exit 0, wall 1926 ms, peak group RSS sampled 1.77 GiB, affinity [0,1], MALLOC_ARENA_MAX=2, leader reaped, no group members left).
3. Sealed receipt/SEALED_BunLowerSupport.json: source cde92558...dfa, olean 903116ca...068, log 5bb63fa7...c45, plus compile-receipt hash e3e695b4...9eb.
4. Scoped #print axioms under the same runner/caps (audit/LowerSupportAxioms.lean, receipt/1794013299582232650_axioms_LowerSupport.json, EXIT 0):
   - Bun.stf_lower_parts:     [propext, Classical.choice, Quot.sound]
   - Bun.stf_lower_support:   [propext, Classical.choice, Quot.sound]
   Only the three allowed axioms; no sorry/admit/new axiom/unsafe/partial/native_decide/extern/implementedBy.
5. checker.sh BunLowerSupport by MODULE name, pinned lean 4.34.1 bin, full LEAN_PATH: receipt/1794013303529678951_leanchecker_BunLowerSupport.json, EXIT 0.
6. Post-checker hash stability: src/olean/log sha256 identical to sealed values.
7. verify_frozen.py after -> {"count": 759, "mismatches": []} (1794013314.5).
8. ARTIFACTS.json manifest: 12 entries, all 64-hex sha256, INCLUDING receipt-JSON hashes; not self-referential.

## Scope honesty
ONE recursive theorem delivered: Bun.stf_lower_support (ALL n u j k : Nat, w : Asg n j, sigma : Bool, k ∈ sval sigma (stf n u j w) -> u ≤ k), via the exact unchanged stf recurrence: n=0 branch, all u/j including outside n, source branch (startST via r14 startST_support), below-source empty branch, successor restricted-assignment branch (stepU via r12 stepU_lower_closed), and inactive out-of-range pass-through. In-module supporting lemma: Bun.stf_lower_parts (componentwise induction invariant). No extra answer hypotheses, no proxy, no enumeration-as-axiom; conclusion proved, not assumed. stf/startST/stepU/ind/sval/Asg untouched.

## Development-import scope (per TASK)
check.sh imports own build + verified r14/r12/r10/r7/r5/r2/r1 production builds and pinned mathlib d13f23b7 prebuilts. Development-import reuse, NOT a fresh all-source extracted replay; no baseline rebuild performed.

## Unpaid remainder (exact; credit 0, 52/60 unchanged)
old-index stability; new-index indicators; literal state-membership iff actualReach joint induction; fresh-token fiber counts; corrected reflection dominance; terminal payoff; cardinality endpoint (382297 main statement); deep audits/negative controls; fresh extracted all-source replay; independent formal review; paper; acceptance. False old flip-fiber-equality/both-full claims not used. Crown r22 / discovery r368 untouched (no read/hash/glob/poll).
