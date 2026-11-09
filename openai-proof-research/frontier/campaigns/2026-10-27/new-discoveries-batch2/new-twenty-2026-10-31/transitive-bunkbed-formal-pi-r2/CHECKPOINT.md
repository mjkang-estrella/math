# CHECKPOINT — transitive-bunkbed-formal-pi-r2 (Pi GLM-5.3-Flash, high thinking)

Campaign 52/60 beyond 39 prior. Credit 0. Lane-local work only. Protected lanes untouched.

## Verified frozen inputs
- `frozen-verify-pass1.json`: 341/341 paths+sha256 OK (pass 1, before math reads).
- bootstrap receipt: `bootstrap-receipt.json` (first command, preserved).

## Strict compile table (true exits from runner receipts; -DwarningAsError=true)
| module | state | receipt |
|---|---|---|
| BunkbedBase (frozen r1 copy) | EXIT=0 (root-matched) | (r1-era, hash-matched) |
| BunkbedCount (root-repaired copy) | EXIT=0 | receipt/1793971701445791038_lean_BunkbedCount.json |
| BunState (NEW) | EXIT=0 | receipt/1793977325270166387_lean_BunState.json |
| BunReach (NEW) | EXIT=0 | receipt/1793982946478871956_lean_BunReach.json |
| BunBridge (NEW, part 1: wres/wres_res/wres_agree) | EXIT=0 | receipt/1793985062185918452_lean_BunBridge.json |

## Mathematical content PROVED (all in compiled sources)
- BunState: `Win/Asg`, `res`, `fresH/fresV`, `hor` (= decide of Nonempty of filtered attach),
  `ind x y z = (if z then x||y else x, if z then x||y else y)`, `stepU`, `startST`, `stf`, `sval`.
- BunReach: `ind_fst/ind_snd` (exact new-pair semantics: z → both layers get x∨y; ¬z → x,y),
  `ind_fst_or/vert`, `ind_snd_or/vert`, `startST_congr`, `hor_congr` (Finset.filter_congr +
  decide_eq_true/false + pointwise agreement), `stf_congr` (window-agreement invariance, all j).
- Key API facts pinned for this toolchain (Mathlib 4.34.1 pin): NO `Finset.any/isEmpty/contains`;
  `decide_eq_true/decide_eq_false` fine; `if_pos/if_neg/dif_pos/dif_neg` DEPRECATED (warningAsError) —
  use `split`/`simp only [..]`/`decide_eq_true` instead; `simp only` + `exact Iff.rfl` closes
  Bool-ite goals after decide rewrites; `congrArg (fun S : Finset _ => decide S.Nonempty)` for
  decide-of-Nonempty congruence; prod goals: rewrite componentwise via `rw` of pointwise hyps.

## Remaining plan (approved route, TASK.txt "Approved ordinary proof")
1. Bridge lemmas (BunReach or new BunBridge):
   a. † crossing-free pair: `k ∈ (stf n u j (res..)).1 ∧ k ≠ j+1 → k ∈ (stf n u (j+1) w).1` etc. —
      actually needed shape: stf value ⊆ Finset.Iic and the RT-derivation induction:
      `Reach n ω (u,false) (j,l) ↔ (stf n u j (resToAsg ω j)).l = true` where resToAsg ω j := 
      fun t => ω t.1 restricted to tmax ≤ j. Prove by induction on j via `reach_char` (base) +
      `ind_fst/ind_snd` + `stf` unfold; the ← direction needs reach_char ∃-witness transfer;
      the → direction is the ⟨⊆⟩ RT-induction using ind_fst_or/vert + hor soundness
      (hor = true ⟹ ∃ i ∈ p.l ... via Finset.filter Nonempty iff).
   b. `stf n u j w ⊆ Finset.Iic j` (needed to quote reach_agree with c := j).
2. Count layer (BunCount.lean):
   - layer-flip `flipT : Token n → Token n` (Σinl: !layer; Σinr: id), involutive `flipT_flipT`;
   - `flipAsg w t := w (flipT t)`, involution on Asg n j;
   - swap lemma `stf n u j (flipAsg w) = ((stf n u j w).2, (stf n u j w).1)` — induction on j,
     using startST/hor/stepU layer symmetry; CAREFUL: hor R-set layer structure and the
     res/fresH commute with flip (fresH l ↔ fresH !l), startST vertical bit unchanged (vtok fixed).
   - fiber cardinalities μ_j(a,b) := card {w : Asg n j | pattern}; dominance μ(T,F) ≥ μ(F,T) via
     the flip injection (flipAsg maps pattern (a,b) bijectively to (b,a)) — NOTE: this gives
     EQUALITY μ(a,b) = μ(b,a) directly by involution+swap lemma — the "D-identity".
   - terminal: card{ω : (v,F)-reach} − card{ω : (v,T)-reach} = card{pattern(T,F)} − card{pattern(F,T)}
     by partitioning Asg n v into the 4 patterns (TT,TF,FT,FF) — equality of the two cards on
     TT/FF classes, difference only TF vs FT.
3. Endpoint (BunCount or BunEnd):
   - coarea: card{ω : Out n | P ω} = card{w : Asg n v // P-window w} * 2^(card of tokens tmax > v)
     via Equiv.sumCompl on the token index by (tmax ≤ v); the window-restriction equiv.
   - final: card{ω : Reach (u,false)→(v,false)} ≥ card{ω : Reach (u,false)→(v,T)} for ALL n,u,v
     (cases: v=u trivial both-full; v<u via bridge+count; u>v or u=v handled by reach_ge/monotone
     structure — both events then determined by prefix ≤ u ... handle by same argument with
     min index; n=0 vacuous Fin).
   - This is the literal bunkbed inequality in the E7 token model, all-n, fixed source/target.
4. Fresh replay from empty build dir; audits (per-TASK checklist); SUMMARY/RESULTS.

## Session log addendum (bridge attempt)
- BunBridge part 1 (wres + restriction + agreement) compiled EXIT=0.
- Bridge kernel designed and verified on paper: the \u2792 (bit\u2192RT) direction needs the 3-part joint induction (bit\u2192RT, memb-F\u2192RT, memb-T\u2192RT) because the hor-witness needs membership\u2192RT at the previous level; the z-branch resolves as x=T\u2192F-path, x=F\u2227y=T\u2192horT-arc then vert-flip, x=F\u2227y=F\u2192A'F-contr. NO circularity: ind_fst gives A'=T \u27fa x\u2228(z\u2227B'), and under z, A'=B'=x\u2228y so x=F \u27f9 y=T forced. The \u2791 (RT\u2192bit) direction: RT-derivation induction, final-arc case split via `arc_cases`, horizontal case needs the i<j witness fed to ind_fst_or/vert via hor faithfulness (filter Nonempty mem\_filter extraction), vertical case via ind\_snd\_vert/ind\_fst\_vert.
- stf level-bound: formulate as membership \u27f9 index \u2264 level per component (avoids Iic API risk); stepU membership needs `simp only [stepU]` then split on the Bool cond `a = true`.

## Session log (key burns)
- BunReach: ~12 compile cycles; main traps: deprecated if/dif lemmas (warningAsError), rename_i
  arity, `first`+unusedTactic linter, hor_congr needing per-instance application (false/true
  separately), `res`-swap direction in stf_congr succ case (ih w w' not w' w).
- BunState/BunReach receipts recorded above; no lane-external writes at any point.
