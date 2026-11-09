# MathDB 347063 — Lean formalization status (partial)

Credit 0. Nothing here is claimed as a new result: part (a) is public (Cusenza et al.,
as the reviewer states) and part (b) is not formalized at all.

## Source check (required by TASK.txt step 1)

I read `inputs/sources/` Definition 1.1 and section 1.2. The formal model in
`src/ZeckBase.lean` matches the source exactly:

* `F 1 = 1`, `F 2 = 2`, `F (i+1) = F i + F (i-1)` (`F i := Nat.fib (i+1)`);
* the start is `n` copies of `F 1` — `start n = Finsupp.single 1 n`;
* moves `A1: F1,F1 -> F2`; `Cons i (i>=2): F(i-1),F i -> F(i+1)`;
  `Split 2: F2,F2 -> F1,F3`; `Split i (i>=3): F i,F i -> F(i-2),F(i+1)`;
* Split Smallest priority: smallest legal split, else `A1`, else smallest legal combine;
* Combine Smallest priority: `A1`, else smallest legal combine, else smallest legal split.

**Difference found (corpus defect).** The MathDB record says the game "starts from the
Zeckendorf decomposition of `n`". Under Definition 1.1 that position has *no legal move*:
every count is at most 1 and no two consecutive indices are occupied, so there is no
`A1`, no `Cons` and no `Split`. The game therefore has zero moves, not a linear number.
The source itself starts at `n` copies of `F 1`. This is formalized, not merely asserted:
`Zeck.zeckendorf_start_has_no_move`, `Zeck.SS_zeckendorf_zero`,
`Zeck.CS_zeckendorf_zero`. It is a transcription error and earns nothing.

## Green modules (compile exit 0, kernel check exit 0, axioms audited)

| module | compile | check | olean sha256 |
|---|---|---|---|
| `ZeckBase` | `base05` | `basecheck05` | `c8126653…cc2196` |
| `ZeckStrategy` | `strat11` | `stratcheck11` | `e043602f…f2f75b` |
| `ZeckControls` | `ctrl06` | `ctrlcheck06` | `1e3dadc4…f8095f` |
| `ZeckPotential` | `pot05` | `potcheck05` | `275678f2…b7e16c` |
| `ZeckBound` | `bnd02` | `bndcheck02` | `ab145ab9…c986275` |
| `ZeckAudit` | `audit01` | `auditcheck01` | `0014fb72…d00f4f` |

`ZeckAudit` prints axioms for every main theorem; each depends on exactly
`[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, `axiom`, `unsafe` or
`native_decide` occurs anywhere in `src/`.

All builds ran through `check32.sh` / `checker32.sh` one at a time, with the lane's
limits (CPU 115 s, 6 GiB, `-j1`, `-M3500`, `LEAN_NUM_THREADS=1`,
`-DwarningAsError=true`). Peak sampled group RSS was below 2.3 GiB; nothing was killed.

## What is proven

**Step 1 — game model (`ZeckBase`).** Positions are finitely supported `ℕ → ℕ`.
Value `val a = Σ a_i F_i` is invariant under every move. Chips decrease by 1 under
`A1`/`Cons` and are preserved by splits. Termination is established with the integer
potential `M a = Σ a_i Wt i` where `Wt 1 = 4`, `Wt 2 = 7`, `Wt i = i+5` (`i ≥ 3`):
every legal move drops `M` by at least 1 (`M_doA1`, `M_doCons`, `M_doSplit2`,
`M_doSplitG`, `M_doSplit`). Also `terminal_le_one` and the index bound `idx_bound`
(`F i ≤ n` for any occupied index).

**Step 2 — the two strategies (`ZeckStrategy`).** `smallestSplit` and `smallestCons`
are `Nat.find` over the legal-move predicates, with the specification that they return
the smallest legal index and are `none` exactly when no such move exists. `stepSS` and
`stepCS` implement the source priorities literally, including the stuck case (`stepSS a = a`
when no move is legal). `gameLen` is `Nat.find` over `exists_terminal` — the *actual*
number of steps, not a fuel bound. `SS n` and `CS n` are `gameLen` from `start n`.

**Step 3 — small exact controls (`ZeckControls`).**
`SS 2 = 1`, `SS 3 = 2`, `SS 4 = 3`, `CS 2 = 1`, `CS 3 = 2`, `CS 4 = 3`, each by proof
from explicit intermediate positions (`e1 n`, `e2 a b`, `e12 a b`, …). These agree with
the reviewer's paper checks `n=2,3,4`.

**Step 4 — the exact potential (`ZeckPotential`).** With
`phi = (1+√5)/2`, `psi = phi - 1`, `s = 1 - phi = -psi`, and
`w j = j + 2 + psi * s^j`:

* `w 1 = phi^2`;
* `w_drop_A1 : 2 w 1 - w 2 = 1`;
* `w_drop_split2 : 2 w 2 - w 1 - w 3 = 1`;
* `w_drop_splitG i : 2 w i - w (i-2) - w (i+1) = 1` for `i ≥ 3`;
* `w_drop_cons i : w (i-1) + w i - w (i+1) = i` for `i ≥ 2`.

These are polynomial identities in `phi`, `psi`, `s`, derived from `phi^2 = phi + 1`,
`psi = phi - 1`, `s = 1 - phi`. Hence `Phi a = Σ a_j w j` satisfies, for every legal move,

* `Phi_doA1 : Phi (doA1 a) = Phi a - 1`,
* `Phi_doCons : Phi (doCons a i) = Phi a - i`,
* `Phi_doSplit : Phi (doSplit a i) = Phi a - 1`.

With `dropSS a` = 1 for a split or `A1`, `i` for `Cons i`, and 0 when stuck,
`Phi_stepSS : Phi (stepSS a) = Phi a - dropSS a`, and by telescoping
`Phi_run : Phi (run stepSS (start n) k) = Phi (start n) - Σ_{j<k} dropSS (run … j)`.

**Step 4b — the bound (`ZeckBound`).** `w j > 0` for every `j` (since
`|psi * s^j| ≤ psi < 1`), so `Phi ≥ 0`. Every legal move drops `Phi` by at least 1, so

* `SS_eq : (SS n : ℝ) = phi^2 * n - Phi (final) - Σ_{j<SS n} (dropSS - 1)`;
* `SS_deficit : phi^2 * n - (SS n : ℝ) = Phi (final) + Σ_{j<SS n} (dropSS - 1)`;
* `SS_le_phi_sq : (SS n : ℝ) ≤ phi^2 * n`.

So the *upper* half of part (a) is formalized, and in a stronger form than the
reviewer's `SS n = phi^2 n + O(log^2 n)` needs.

## What is unpaid

**Part (a), lower half.** `SS n ≥ phi^2 n - O(log^2 n)` is not proved. It needs:

1. the Phase 1 / Phase 2 split — Phase 1 runs while a split or `A1` exists and ends at a
   position `b` with all `b_j ∈ {0,1}`; in Phase 1 `dropSS = 1` at every step, so the
   exact Phase 1 count is `T(n) = phi^2 n - Phi(b)` (this is the reviewer's formula and
   is *not* formalized — `SS_eq` above refers to the final position, not to `b`);
2. `Phi(b) = Σ b_j w j = O(log^2 n)`, using `idx_bound` (all occupied indices are
   `O(log n)`) and `w j ≤ j + 3`;
3. the reviewer's Lemma T (from `c` chips at indices `≤ L`, every continuation has
   `O(cL)` moves) to bound Phase 2. That needs the index-sum monotonicity
   (`A1`: 0, `Cons i`: `2-i ≤ 0`, `Split 2`: 0, `Split i≥3`: `-1`) plus the
   `Split 2` counting argument.

The potential machinery for (1) is in place; the phase decomposition and Lemma T are not.

**Part (b), entirely.** The `READY(p; N, Z, O)` summary with lower state `L ∈ [0, F(p-1))`,
the rotation `L ↦ L + F(p-2) mod F(p-1)`, the chip balance `F_p - 1` splits per cycle,
the level assembly with its error, the endgame by cases, and the constant
`c = 5/2 - phi + Σ_{j≥2} 1/F_{2j} = 1.2064812…` with `1.206 < c < 1.207` are all
unformalized. The reviewer's erratum (endgame Case 3 with `m = 3` exits via
`B_{p+2}(r' + F_{p-1}, M+1, 0)` because `C_{p+1}` fires before `S_{p-2}`) was noted but
there is no code for it yet.

**Endpoint.** `Zeck.split_smallest_asymptotic` and `Zeck.combine_smallest_asymptotic`
are not stated. No weakened placeholder, no `sorry`, and no added premise was used.

## Notes for the next lane

* `Nat.log2` lemma names differ from the ones I probed; `Mathlib.Analysis.SpecialFunctions.Log.Basic`
  and `Mathlib.Data.Nat.Log` are both importable, `Real.log_le_log`, `Real.log_pow`,
  `Real.log_pos` exist, but `Nat.pow_log2_le`, `Nat.log2_le_iff`, `Nat.lt_pow_iff_log2_lt`,
  `Real.log_two_pos` do **not** exist in this toolchain. Check names before writing.
* `Finsupp.update_apply` is stated as `(f.update a b) i = if i = a then b else f i`.
  Field notation on the `Pos` synonym fails; use the function-argument form.
* `if_neg` and `if_false` are deprecated here (`ite_eq_right`, `ite_false`); both are
  errors under `-DwarningAsError=true`. For nested updates, `rw [Finsupp.update_apply]`
  twice followed by `split_ifs` avoids the deprecation entirely.
* `nlinarith` does not reduce `Nat.cast` numerals (`↑1`, `↑2`, `↑3`) or `s^1`; run
  `norm_num` / `simp only [pow_one]` first, or state the auxiliary identity as a `calc`.
* `Mathlib.Tactic.Omega`'s olean is absent, but core `omega` works.
* `Finsupp.update` is noncomputable, so any definition built on it needs `noncomputable def`.
