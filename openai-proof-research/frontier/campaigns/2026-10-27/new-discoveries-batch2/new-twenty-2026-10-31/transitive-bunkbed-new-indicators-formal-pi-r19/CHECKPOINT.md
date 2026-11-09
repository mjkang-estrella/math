# CHECKPOINT — transitive-bunkbed-new-indicators-formal-pi-r19

Status: SEALED. Work yourself, no children; lane writes only via write_lane.py
(src attempt written directly in-lane before any inspection, per TASK order).

## Sequence (receipt stamps UTC-epoch)
1. `bootstrap.py` -> bootstrap-receipt.json (905 frozen inputs registered; source hashes in ROOT-PREPARATION.json).
2. `verify_frozen.py before` -> exit 0, count 905, mismatches 0 (frozen-before.json).
3. WRITE src/BunNewIndicators.lean (genuine direct new-index indicator attempt) then
   `check.sh BunNewIndicators` before any further inspection: exit 1 with real diagnostics
   (dot-notation `h.elim` on an elaboration metavariable in the two `Iff` pair projections).
4. Repair from actual diagnostics only (`h.elim id` -> `False.elim h`); recheck: exit 0 strict
   warningAsError, olean built. Receipts 1794022646694422549 (failed, preserved) and
   1794022734043671290 (success).
5. `checker.sh BunNewIndicators` (actual module checker, pinned PATH/env): exit 0. Receipt 1794022802497790695.
6. Scoped `#print axioms` on ALL 7 new declarations (audit/axaudit_BunNewIndicators.lean via runner).
   Three runner attempts aborted -6 (lean thread creation EAGAIN at the 12GiB AS margin; the audit
   invocation lacked the build's `-j1`; all three receipts preserved). With `-j1`, same caps: exit 0;
   every declaration exactly within {propext, Classical.choice, Quot.sound}; no
   sorry/admit/newaxiom/unsafe/partial/native_decide/extern/implementedBy.
   Receipt 1794023191162840284.
7. `verify_frozen.py after` -> exit 0, count 905, mismatches 0 (frozen-after.json).
8. Hashes of source/olean (postchecker)/logs/receipt JSONs in manifest.json and result-382297.json.

## Sealed target
Bun.stf_new_mem_fst_iff / Bun.stf_new_mem_snd_iff : for ALL n u j : Nat, w : Asg n (j+1),
hu : u < j+1, hjn : j+1 < n, with p = stf n u j (res n j w), x/y the hor entries, z the fresV bit:
  j+1 in (stf n u (j+1) w).1 <-> x = true OR (z = true AND y = true)
  j+1 in (stf n u (j+1) w).2 <-> y = true OR (z = true AND x = true).
Active branch only; new-index absence in the old prefix from paid Bun.stf_upper_support (r9);
pure Boolean direct forms ind_fst_direct/ind_snd_direct by kernel cases; coupled
Bun.ind_fst/ind_snd not used; no Reach/count expansion; existing definitions untouched.

## Jobs
All runner runs reaped via Popen.poll returncode (leader_reaped note in each receipt;
group_members_left []); no zombies, no invented cgroup claims.

## Unpaid (EXACT list, credit 0; 52/60 unchanged)
source/reset membership identities; literal state-membership iff Reach joint induction;
token-fiber cardinalities; corrected reflection dominance; terminal payoff; literal
cardinality endpoint; full module-origin/body/type/safety audit; negative controls; fresh
extracted replay; independent review; paper; acceptance. Never revive rejected same-source
flip-fiber equality or both-full claims.

Seal target reached. STOP.
