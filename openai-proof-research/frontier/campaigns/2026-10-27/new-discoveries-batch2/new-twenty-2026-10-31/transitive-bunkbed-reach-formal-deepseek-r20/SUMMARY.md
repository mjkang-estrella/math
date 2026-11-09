# MathDB 382297 — r20 lane SUMMARY (transitive-bunkbed-reach-formal-deepseek-r20)

Credit 0. Campaign 57 of 80 unchanged. Acceptance is root-only. Pi DeepSeek V4.1 Flash,
high thinking, work done directly; no child agents, no fallback model.

## What is proven and green (compile exit 0 AND kernel-check exit 0, axioms audited)

### Step 0 — baseline replay
All fourteen baseline modules in `BASELINE.json` build order were compiled and
kernel-checked from an empty `build/` through `check32.sh` / `checker32.sh`
(`base_compile_MODULE` / `base_check_MODULE`). Every compile and every kernel check
exited 0. Baseline sources were not modified.

### Step 1 — literal Reach bridge (the assigned step target)
`src/BunReachSupport.lean` (compile `r20_compile_support3`, check `r20_check_support3`):
`htok_congr`, `wres_fresH`, `wres_fresV`, `fresV_congr`, `fresV_bit_congr`,
`startST_mem_fst`, `startST_mem_snd`, `startST_mem`, `reach_same_index`,
`stepU_new_ind_fst`, `stepU_new_ind_snd`.

`src/BunReachBridge.lean` (compile `r20_compile_bridge4`, check `r20_check_bridge4`):
* `Bun.stf_reach_strong` : for `j < n`,
  `i.val ∈ sval σ (stf n u.val j (wres n j ω)) ↔ u.val ≤ i.val ∧ i.val ≤ j ∧ Reach n ω (u,false) (i,σ)`.
* `Bun.stf_reach_iff` : `i.val ∈ sval σ (stf n u.val j (wres n j ω)) ↔ i.val ≤ j ∧ Reach n ω (u,false) (i,σ)`.
* `Bun.stf_reach_endpoint` : the `i = j` specialization,
  `v.val ∈ sval σ (stf n u.val v.val (wres n v.val ω)) ↔ Reach n ω (u,false) (v,σ)`.
* `Bun.reach_of_lt` : `v < u → ¬ Reach n ω (u,false) (v,σ)` (the `v < u` case).
* `Bun.reach_self` : `Reach n ω (u,false) (u,σ) ↔ σ = false ∨ ω (vtok u) = true` (the `v = u` case).

The proof follows the brief's joint prefix induction: state→Reach through the closed
indicator forms `X ∨ (Z ∧ Y)` / `Y ∨ (Z ∧ X)`, and Reach→state by an inner
`ReflTransGen` derivation induction with the generalized low-endpoint bound. The cyclic
`reach_char` equations were not rewritten (the `X=Y=0, Z=1` spurious fixed point is
avoided).

Axiom audit `src/AuditBunReachBridge.lean` (compile `r20_audit_bridge1`, check
`r20_checkaudit_bridge1`): every theorem depends only on `propext`, `Classical.choice`,
`Quot.sound`.

### Partial Step 2 — fresh-token split only
`src/BunCountFresh.lean` (compile `r20_compile_fresh2`, check `r20_check_fresh1`):
`Fresh n m`, `freshHAt`, `freshVAt`, `ext`, `ext_old`, `ext_fresh`, `res_ext`,
`ext_res`, the bijection `asgSuccEquiv : Asg n (m+1) ≃ Asg n m × (Fresh n m → Bool)`,
and the cardinality recursion `card_asg_succ`.
Audit `src/AuditBunCountFresh.lean` (compile `r20_audit_countfresh1`, check
`r20_checkaudit_countfresh1`): only `propext`, `Classical.choice`, `Quot.sound`.

## What is NOT proven in this lane (unpaid)

* The rest of Step 2: the model bijection `Fresh ≃ (Fin (m+1) × Bool) ⊕ Unit` with
  `card Fresh = 2(m+1)+1`; the integer fiber counts
  `2^(2m-a-b)·(2, 2^a-1, 2^b-1, 2^(a+b+1)-2^a-2^b)`; the initial biased law; the
  reflection DOMINANCE induction; the terminal payoff; the outside-window factors.
* Step 3: the literal endpoint `Bun.bunkbed_E7_transitive` is not proved here.
  Root reports the counting inequality and endpoint were proved and kernel-checked in
  another lane; the next lane does the final assembly.

Work was stopped on root instruction; `BunCountFresh` is kept exactly as it compiled.

## Failures kept honestly (true exits)

* `r20_compile_support1` exit 1 (rewrite/`omega` failures), `r20_compile_support2`
  exit 1 (unsolved goal + "No goals to be solved").
* `r20_compile_bridge1` exit 1 (deprecated `if_pos`/`if_neg`, `omega`, pattern
  mismatches), `r20_compile_bridge3` exit 1 (`omega` on an incompletely destructed
  tuple). A large patch attempt produced an empty file that compiled trivially; that
  receipt was identified as void and the module was rewritten from scratch, not counted.
* `r20_compile_fresh1` exit 1 (deprecated `dif_pos`/`dif_neg`, missing `DecidableEq`
  for `card_fun`, and a redundant `rfl`).

## Rules observed
Lean ran only through `check32.sh` / `checker32.sh`, one at a time, unique labels.
Specific Mathlib imports only (no `import Mathlib`). No `sorry`, `admit`, `axiom`,
`unsafe`, `native_decide`; no target weakening, no conclusion-bearing premise, no proxy
definition. Authored files written through `write_lane.py`; local non-Lean work through
`run.py`. No peers touched, no network, no git, no installs.
