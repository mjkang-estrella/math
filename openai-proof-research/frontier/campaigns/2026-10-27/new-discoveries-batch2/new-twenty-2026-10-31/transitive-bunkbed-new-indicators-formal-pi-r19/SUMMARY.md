# SUMMARY — r19 transitive-bunkbed-new-indicators (MathDB 382297 auxiliary)

Delivered: `src/BunNewIndicators.lean`, module `BunNewIndicators`, strict warningAsError build
exit 0 (Lean 4.34.1, -j1 -M3500), actual `checker.sh BunNewIndicators` exit 0, scoped axiom audit
exit 0 with all seven new declarations within {propext, Classical.choice, Quot.sound} only.

Main results `Bun.stf_new_mem_fst_iff` / `Bun.stf_new_mem_snd_iff` (DIRECT NEW-INDEX INDICATOR
IDENTITIES of the actual active prefix recurrence): for all `n u j : Nat`, `w : Asg n (j+1)`,
`hu : u < j+1`, `hjn : j+1 < n`, with `p = stf n u j (res n j w)`,
`x = hor (m:=j+1) hjn p.1 false w`, `y = hor (m:=j+1) hjn p.2 true w`,
`z = w (fresV (n:=n) (m:=j+1) hjn)`:

  `j+1 ∈ (stf n u (j+1) w).1 ↔ x = true ∨ (z = true ∧ y = true)`
  `j+1 ∈ (stf n u (j+1) w).2 ↔ y = true ∨ (z = true ∧ x = true)`

Mechanism: active branch `u < j+1 < n` gives `stf n u (j+1) w = stepU (j+1) p.1 p.2 x y z` by the
exact definition (dite rewrites, r18 pattern); component `i` is
`if (ind x y z).i then insert (j+1) _ else _`, so `j+1` enters iff the indicator fires
(`mem_update_self`, `stepU_new_mem_fst/snd`); absence of `j+1` from the old prefix components is
the PAID r9 `Bun.stf_upper_support` (`k ≤ j` there), not an assumed premise. The direct indicator
forms `ind_fst_direct`/`ind_snd_direct` are pure Boolean case splits; the coupled
`Bun.ind_fst/ind_snd` equations are not used and the least-Reach closure is not assumed.
No below-source/reset/out-of-range new-index claims; old-index stability not reproved; no
Reach/count expansion. Existing definitions untouched; imports BunOldStable/BunUpperSupport/
BunState via supplied readonly builds; no baseline replay.

905 frozen inputs verified before and after; all jobs reaped; failed first build and three
AS-margin aborted audit attempts preserved honestly. Credit 0; 52/60 unchanged. Seal target
reached; stopped.
