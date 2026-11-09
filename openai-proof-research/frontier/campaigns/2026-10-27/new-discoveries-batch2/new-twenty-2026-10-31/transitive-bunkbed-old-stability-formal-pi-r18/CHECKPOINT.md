# CHECKPOINT — transitive-bunkbed-old-stability-formal-pi-r18

Status: SEALED. Work yourself, no children; lane writes only via write_lane.py.

## Sequence (receipt stamps UTC-epoch)
1. `bootstrap.py` -> bootstrap-receipt.json (863 frozen inputs registered; source hashes in ROOT-PREPARATION.json).
2. `verify_frozen.py before` -> exit 0, count 863, mismatches 0 (frozen-before.json).
3. WRITE src/BunOldStable.lean (genuine full-recurrence proof attempt) then `check.sh BunOldStable` before any further inspection: exit 1 with real diagnostics (deprecated if_pos/if_neg/dif_pos/dif_neg; Finset.not_mem_empty unknown).
4. Repair from actual diagnostics only (ite_eq_left/ite_eq_right/dite_eq_left/dite_eq_right; Finset.notMem_empty); recheck: exit 0 strict warningAsError, olean built. Receipt 1794021119795084948.
5. `checker.sh BunOldStable` (actual module checker, pinned PATH/env): exit 0. Receipt 1794021125539540704.
6. Scoped `#print axioms` on ALL 6 new declarations (audit/axaudit_BunOldStable.lean via runner): exit 0; every declaration exactly within {propext, Classical.choice, Quot.sound}; no sorry/admit/newaxiom/unsafe/partial/native_decide/extern/implementedBy. Receipt 1794021172405264577.
7. `verify_frozen.py after` -> exit 0, count 863, mismatches 0 (frozen-after.json).
8. Hashes of source/olean/logs/receipts recorded in manifest.json and result-382297.json; rehash-after-checker consistent (olean mtime 1794021120 < checker stamp).

## Sealed target
Bun.stf_old_mem_iff : ALL n u j k : Nat, w : Asg n (j+1), sigma : Bool, k <= j,
  k in sval sigma (stf n u (j+1) w) <-> k in sval sigma (stf n u j (res n j w)).
Full recurrence, no range hypothesis; below-source dummies, source reset, active stepU update (paid r17 helper Bun.stepU_old_mem_iff, source 5649af1f7374c907fb0715b2266ac3dcfa05359b76ff27d6672f94332cb3b543), out-of-range identity; both layers.

## Jobs
All runner runs reaped via Popen.poll returncode (leader_reaped note in each receipt; group_members_left []); no zombies, no invented cgroup claims.

## Unpaid (EXACT list, credit 0; 52/60 unchanged)
new indicators; actual prefix-membership iff Reach joint induction; token fibers; correct reflection dominance; terminal payoff; literal cardinality endpoint; full module-origin/body/types/safety audit; negative controls; fresh extracted replay; independent review; paper; acceptance.

Seal target reached. STOP.
