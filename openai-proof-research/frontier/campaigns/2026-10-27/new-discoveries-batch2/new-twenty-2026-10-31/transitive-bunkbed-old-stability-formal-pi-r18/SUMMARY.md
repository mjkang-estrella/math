# SUMMARY — r18 transitive-bunkbed-old-stability (MathDB 382297 auxiliary)

Delivered: `src/BunOldStable.lean`, module `BunOldStable`, strict warningAsError build exit 0
(Lean 4.34.1, -j1 -M3500), actual `checker.sh BunOldStable` exit 0, scoped axiom audit exit 0 with
all six new declarations within {propext, Classical.choice, Quot.sound} only.

Main theorem `Bun.stf_old_mem_iff` (full OLD-INDEX MEMBERSHIP STABILITY of the actual recursive `stf`):
for all `n u j k : Nat`, `w : Asg n (j+1)`, `sigma : Bool`, `k <= j`,
`k in sval sigma (stf n u (j+1) w) <-> k in sval sigma (stf n u j (res n j w))`.
No n/u/j range premise. Branch coverage: below-source dummy pair (`j+1 < u`), source reset
(`j+1 = u`, start-state layers contain at most the new index), active update
(`u < j+1 < n`, decided by the paid r17 pure step helper `Bun.stepU_old_mem_iff`,
source 5649af1f7374c907fb0715b2266ac3dcfa05359b76ff27d6672f94332cb3b543), and the
out-of-range verbatim identity (`n <= j+1`). Both layers via `sval`.
Supporting declarations: `stf_dummy_of_lt`, `startST_fst`, `startST_snd`, `sval_pair_empty`,
`startST_not_mem_old` (component corollaries; the full recurrence theorem is delivered).

Existing definitions (stf/res/startST/stepU/sval/Asg) untouched; imports only
BunStepOld/BunState plus their transitive readonly builds; no baseline rebuild; no copied oleans
(new build from empty). 863 frozen inputs verified before and after; all jobs reaped; writes only
via write_lane.py. Credit 0; 52/60 unchanged. Seal target reached; stopped.
