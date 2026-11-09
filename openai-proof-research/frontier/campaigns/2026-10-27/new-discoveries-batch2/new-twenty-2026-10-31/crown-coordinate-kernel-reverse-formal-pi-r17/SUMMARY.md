# r17 SUMMARY — crown coordinate kernel reverse (MathDB 369163 aux)

## Executed (actual, on-disk)

1. `bootstrap.py` — receipt `bootstrap-receipt.json` preserved untouched.
2. `verify_frozen.py before` — 866 paths, 0 mismatches.
3. **Difference lemma sealed**: `src/CrownVCoordDiff.lean`, strict build
   (`lean -j1 -M3500 -DwarningAsError=true`), exit 0,
   receipt `receipt/1794003662473566654_lean_CrownVCoordDiff.json`.
   `CrownV.coordKill_sub_mem_span T p : p - coordKill T p ∈ Ideal.span (coordGens T)`
   for ARBITRARY `p : PolyRing n K` (induction on MvPolynomial generators
   C/add/mul_X; no constant-only or variable-only reduction; no finiteness,
   degree bound, primality or char restriction; all n incl 0, empty/full T).
4. **Reverse + equality sealed**: `src/CrownVCoordKernelEq.lean`, exit 0,
   receipt `receipt/1794004034431699188_lean_CrownVCoordKernelEq.json`.
   `CrownV.coordKer_le_span` (reverse inclusion) and
   `CrownV.coordKill_ker_eq` (kernel EQUALITY, by `le_antisymm` with the
   sealed r16 forward `CrownV.coordSpan_le_ker`; no new hypotheses).
5. Scoped axiom audit (`audit/CrownVCoordKernelEqAxioms.lean`, runner caps):
   receipt `..._lean_CrownVCoordKernelEqAxioms3.json`, exit 0. All three
   theorems depend only on `[propext, Classical.choice, Quot.sound]`.
6. `leanchecker CrownVCoordKernelEq` (pinned lean 4.34.1 on PATH, runner caps):
   receipt `..._leanchecker_CrownVCoordKernelEq3.json`, exit 0. Source/olean
   SHA-256 re-verified AFTER the checker against the build receipts: all true
   (Diff src f47eb2ad…, olean 1deb5a5a…; Eq src 80c09644…, olean 3ba9b2a2…).
7. `verify_frozen.py after` — 866 paths, 0 mismatches.

Superseded receipts kept honestly: 2 failed diff rounds (elab shape), 1 failed
KernelEq round (none — first pass), 2+2 failed audit/checker env rounds
(LEAN_PATH `$LANE`/`$PACK` unexpanded) before the passing pair.

## Caps / environment

runner.py r6 (CPU 120s, wall 140s, devguard 130s, AS 12GiB, RSS guard 6GiB,
MALLOC_ARENA_MAX=2, ≤2 CPUs, affinity [0,1]); check.sh LEAN_PATH own-build-first
+ r16/r15/r13/r11/r10/r9/r7 + pinned mathlib d13f23b723b8a846827a245b89c10fc7d3f11612;
lean 4.34.1 at dlp-research/.tools/lean-4.34.1-linux. All jobs reaped
(GROUP_MEMBERS_LEFT [] in every receipt); no guards tripped.

## Not done / unpaid (exact)

Fullside primality; noncoordinate families / J-structure / direct colon;
all-field arbitrary homogeneous degree 0..3 incl char 2; quartic EXACT colons /
VIs 4; module-origin/body/safety/fulltype audits beyond the scoped axiom audit
above; negative controls; fresh all-source extracted replay; independent
reviews; paper; full endpoint; acceptance. **Credit 0; campaign 52/60 unchanged.**

No network, git, installs, dependency/shared/parent writes, lane reads beyond
supplied inputs, or protected-lane (tournament-upper-support-r9,
expanded-corpus-r359) access. No sorry/admit/new axioms/unsafe/native_decide.
