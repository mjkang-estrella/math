# Lean source appendix — MathDB 358162

Lean 4.34.1, Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 (see PINS.json). Modules are listed in import order; each block is byte-identical to `src/<Module>.lean`.

### `RomikDefs.lean`

```lean
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Romik's sequence `v(n)` (Krattenthaler–Müller, arXiv:2304.11471, (2.3) and (2.6))

Source, (2.3): `Π₃(N) := ∏_{j=1}^{N} (4j-3)^2`.
Source, (2.6): `v(n) = 2^{n-1} Π₃(n) - (1/2) Σ_{m=1}^{n-1} binom(2n,2m) v(m) v(n-m)`, `v(0) = 1`.

`romikQ` is this recurrence over `ℚ` (so the `1/2` is literal); `romikQ_rec` states it in
the source's form.  `romikQ_int` proves every value is an integer, and `romikV` is that integer.
-/

open Finset

/-- Source (2.3): `Π₃(N) = ∏_{j=1}^{N} (4j-3)^2`. -/
def Pi3 (n : ℕ) : ℕ := ∏ j ∈ Finset.range n, (4 * (j + 1) - 3) ^ 2

/-- Source (2.6), over `ℚ`.  (The sum over `m = 1, …, n-1` is written with `m = i + 1`,
`i : Fin (n-1)`, only to make the recursion structurally visible; `romikQ_rec` restates it.) -/
def romikQ : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      2 ^ n * (Pi3 (n + 1) : ℚ) -
        (1 / 2) * ∑ i : Fin n,
          ((Nat.choose (2 * (n + 1)) (2 * (i.val + 1)) : ℕ) : ℚ) *
            romikQ (i.val + 1) * romikQ (n - i.val)
  decreasing_by all_goals (have := i.isLt; omega)

theorem romikQ_zero : romikQ 0 = 1 := by rw [romikQ]

/-- The source's recurrence (2.6), literally, for `n ≥ 1`. -/
theorem romikQ_rec (n : ℕ) (hn : 1 ≤ n) :
    romikQ n = 2 ^ (n - 1) * (Pi3 n : ℚ) -
      (1 / 2) * ∑ m ∈ Finset.Ico 1 n,
        ((Nat.choose (2 * n) (2 * m) : ℕ) : ℚ) * romikQ m * romikQ (n - m) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [romikQ]
  simp only [Nat.add_sub_cancel]
  congr 2
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_range (fun i =>
      ((Nat.choose (2 * (k + 1)) (2 * (1 + i)) : ℕ) : ℚ) * romikQ (1 + i) * romikQ (k + 1 - (1 + i)))]
  have : k + 1 - 1 = k := by omega
  rw [this]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Nat.add_comm 1 i.val, show k + 1 - (i.val + 1) = k - i.val by omega]

/-- Integrality bridge: every `romikQ n` is an integer. -/
theorem romikQ_int : ∀ n, ∃ z : ℤ, romikQ n = z := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨1, by simp [romikQ_zero]⟩
    choose! z hz using ih
    -- the sum `Σ binom(2n,2m) z_m z_{n-m}` is even
    set S : ℤ := ∑ m ∈ Finset.Ico 1 n, (Nat.choose (2 * n) (2 * m) : ℤ) * z m * z (n - m)
      with hS
    have hsym : ∀ m ∈ Finset.Ico 1 n,
        (Nat.choose (2 * n) (2 * m) : ℤ) * z m * z (n - m) =
          (Nat.choose (2 * n) (2 * (n - m)) : ℤ) * z (n - m) * z (n - (n - m)) := by
      intro m hm
      rw [Finset.mem_Ico] at hm
      have : n - (n - m) = m := by omega
      rw [this, show 2 * (n - m) = 2 * n - 2 * m by omega, Nat.choose_symm (by omega)]
      ring
    have heven : (2 : ℤ) ∣ S := by
      have h2 : ((S : ℤ) : ZMod 2) = 0 := by
        rw [hS]
        push_cast
        refine Finset.sum_involution (fun m _ => n - m) ?_ ?_ ?_ ?_
        · intro m hm
          have := hsym m hm
          have e : ((Nat.choose (2 * n) (2 * m) : ℤ) * z m * z (n - m) : ZMod 2) =
              ((Nat.choose (2 * n) (2 * (n - m)) : ℤ) * z (n - m) * z (n - (n - m)) : ZMod 2) := by
            exact_mod_cast congrArg (fun x : ℤ => (x : ZMod 2)) this
          push_cast at e
          rw [← e, ← two_mul]
          rw [show (2 : ZMod 2) = 0 from rfl, zero_mul]
        · intro m hm hne heq
          apply hne
          rw [Finset.mem_Ico] at hm
          have hm2 : 2 * m = n := by omega
          have hc : (2 : ℕ) ∣ Nat.choose (2 * n) (2 * m) := by
            rw [hm2, ← Nat.centralBinom_eq_two_mul_choose]
            exact Nat.two_dvd_centralBinom_of_one_le (by omega)
          obtain ⟨u, hu⟩ := hc
          rw [hu]; push_cast
          rw [show (2 : ZMod 2) = 0 from rfl]; ring
        · intro m hm
          rw [Finset.mem_Ico] at hm ⊢; omega
        · intro m hm
          rw [Finset.mem_Ico] at hm
          omega
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd S 2).mp h2
    obtain ⟨S', hS'⟩ := heven
    refine ⟨2 ^ (n - 1) * (Pi3 n : ℤ) - S', ?_⟩
    rw [romikQ_rec n hn]
    have hsum : (∑ m ∈ Finset.Ico 1 n,
        ((Nat.choose (2 * n) (2 * m) : ℕ) : ℚ) * romikQ m * romikQ (n - m)) = (S : ℚ) := by
      rw [hS]; push_cast
      refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [Finset.mem_Ico] at hm
      rw [hz m (by omega), hz (n - m) (by omega)]
    rw [hsum, hS']
    push_cast
    ring

/-- Romik's sequence `v(n)` of the source, as an integer. -/
noncomputable def romikV (n : ℕ) : ℤ := Classical.choose (romikQ_int n)

theorem romikV_spec (n : ℕ) : romikQ n = (romikV n : ℚ) := Classical.choose_spec (romikQ_int n)

/-- `smallW p = Σ_{r < (p+1)/4} (∏_{i=1}^{r} (4i-1)^2) / (2r+1)! · T^r` in `F_p[T]`. -/
noncomputable def smallW (p : ℕ) : Polynomial (ZMod p) :=
  ∑ r ∈ Finset.range ((p + 1) / 4),
    Polynomial.C (((∏ i ∈ Finset.range r, (4 * (i + 1) - 1) ^ 2 : ℕ) : ZMod p) *
      (((2 * r + 1).factorial : ℕ) : ZMod p)⁻¹) * Polynomial.X ^ r

/-- The denominators in `smallW` are units: `2r+1 < p`, so `p ∤ (2r+1)!`. -/
theorem smallW_denominator_unit {p : ℕ} (hp : p.Prime) (r : ℕ) (hr : r < (p + 1) / 4) :
    (((2 * r + 1).factorial : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  rw [Nat.Prime.dvd_factorial hp]
  omega
```

### `RomikValues.lean`

```lean
import RomikDefs

set_option linter.unusedSimpArgs false

open Finset

/-! Sanity guards: the source's printed values `v(0), …, v(10)` (source, after (2.6)). -/

theorem romikQ_1 : romikQ 1 = 1 := by
  rw [romikQ_rec 1 le_rfl]; simp [Pi3]

private theorem ch_4_2 : Nat.choose 4 2 = 6 := by decide
private theorem ch_6_2 : Nat.choose 6 2 = 15 := by decide
private theorem ch_6_4 : Nat.choose 6 4 = 15 := by decide
private theorem ch_8_2 : Nat.choose 8 2 = 28 := by decide
private theorem ch_8_4 : Nat.choose 8 4 = 70 := by decide
private theorem ch_8_6 : Nat.choose 8 6 = 28 := by decide
private theorem ch_10_2 : Nat.choose 10 2 = 45 := by decide
private theorem ch_10_4 : Nat.choose 10 4 = 210 := by decide
private theorem ch_10_6 : Nat.choose 10 6 = 210 := by decide
private theorem ch_10_8 : Nat.choose 10 8 = 45 := by decide
private theorem ch_12_2 : Nat.choose 12 2 = 66 := by decide
private theorem ch_12_4 : Nat.choose 12 4 = 495 := by decide
private theorem ch_12_6 : Nat.choose 12 6 = 924 := by decide
private theorem ch_12_8 : Nat.choose 12 8 = 495 := by decide
private theorem ch_12_10 : Nat.choose 12 10 = 66 := by decide
private theorem ch_14_2 : Nat.choose 14 2 = 91 := by decide
private theorem ch_14_4 : Nat.choose 14 4 = 1001 := by decide
private theorem ch_14_6 : Nat.choose 14 6 = 3003 := by decide
private theorem ch_14_8 : Nat.choose 14 8 = 3003 := by decide
private theorem ch_14_10 : Nat.choose 14 10 = 1001 := by decide
private theorem ch_14_12 : Nat.choose 14 12 = 91 := by decide
private theorem ch_16_2 : Nat.choose 16 2 = 120 := by decide
private theorem ch_16_4 : Nat.choose 16 4 = 1820 := by decide
private theorem ch_16_6 : Nat.choose 16 6 = 8008 := by decide
private theorem ch_16_8 : Nat.choose 16 8 = 12870 := by decide
private theorem ch_16_10 : Nat.choose 16 10 = 8008 := by decide
private theorem ch_16_12 : Nat.choose 16 12 = 1820 := by decide
private theorem ch_16_14 : Nat.choose 16 14 = 120 := by decide
private theorem ch_18_2 : Nat.choose 18 2 = 153 := by decide
private theorem ch_18_4 : Nat.choose 18 4 = 3060 := by decide
private theorem ch_18_6 : Nat.choose 18 6 = 18564 := by decide
private theorem ch_18_8 : Nat.choose 18 8 = 43758 := by decide
private theorem ch_18_10 : Nat.choose 18 10 = 43758 := by decide
private theorem ch_18_12 : Nat.choose 18 12 = 18564 := by decide
private theorem ch_18_14 : Nat.choose 18 14 = 3060 := by decide
private theorem ch_18_16 : Nat.choose 18 16 = 153 := by decide
private theorem ch_20_2 : Nat.choose 20 2 = 190 := by decide
private theorem ch_20_4 : Nat.choose 20 4 = 4845 := by decide
private theorem ch_20_6 : Nat.choose 20 6 = 38760 := by decide
private theorem ch_20_8 : Nat.choose 20 8 = 125970 := by decide
private theorem ch_20_10 : Nat.choose 20 10 = 184756 := by decide
private theorem ch_20_12 : Nat.choose 20 12 = 125970 := by decide
private theorem ch_20_14 : Nat.choose 20 14 = 38760 := by decide
private theorem ch_20_16 : Nat.choose 20 16 = 4845 := by decide
private theorem ch_20_18 : Nat.choose 20 18 = 190 := by decide

theorem romikQ_2 : romikQ 2 = 47 := by
  rw [romikQ_rec 2 (by norm_num)]
  simp only [Pi3, Finset.prod_range_succ, Finset.prod_range_zero, Finset.sum_Ico_eq_sum_range,
    Finset.sum_range_succ, Finset.sum_range_zero, romikQ_1, Nat.reduceAdd, Nat.reduceMul,
    Nat.reduceSub, ch_4_2, ch_6_2, ch_6_4, ch_8_2, ch_8_4, ch_8_6, ch_10_2, ch_10_4, ch_10_6, ch_10_8, ch_12_2, ch_12_4, ch_12_6, ch_12_8, ch_12_10, ch_14_2, ch_14_4, ch_14_6, ch_14_8, ch_14_10, ch_14_12, ch_16_2, ch_16_4, ch_16_6, ch_16_8, ch_16_10, ch_16_12, ch_16_14, ch_18_2, ch_18_4, ch_18_6, ch_18_8, ch_18_10, ch_18_12, ch_18_14, ch_18_16, ch_20_2, ch_20_4, ch_20_6, ch_20_8, ch_20_10, ch_20_12, ch_20_14, ch_20_16, ch_20_18]
  norm_num

theorem romikQ_3 : romikQ 3 = 7395 := by
  rw [romikQ_rec 3 (by norm_num)]
  simp only [Pi3, Finset.prod_range_succ, Finset.prod_range_zero, Finset.sum_Ico_eq_sum_range,
    Finset.sum_range_succ, Finset.sum_range_zero, romikQ_1, romikQ_2, Nat.reduceAdd, Nat.reduceMul,
    Nat.reduceSub, ch_4_2, ch_6_2, ch_6_4, ch_8_2, ch_8_4, ch_8_6, ch_10_2, ch_10_4, ch_10_6, ch_10_8, ch_12_2, ch_12_4, ch_12_6, ch_12_8, ch_12_10, ch_14_2, ch_14_4, ch_14_6, ch_14_8, ch_14_10, ch_14_12, ch_16_2, ch_16_4, ch_16_6, ch_16_8, ch_16_10, ch_16_12, ch_16_14, ch_18_2, ch_18_4, ch_18_6, ch_18_8, ch_18_10, ch_18_12, ch_18_14, ch_18_16, ch_20_2, ch_20_4, ch_20_6, ch_20_8, ch_20_10, ch_20_12, ch_20_14, ch_20_16, ch_20_18]
  norm_num

theorem romikQ_4 : romikQ 4 = 2453425 := by
  rw [romikQ_rec 4 (by norm_num)]
  simp only [Pi3, Finset.prod_range_succ, Finset.prod_range_zero, Finset.sum_Ico_eq_sum_range,
    Finset.sum_range_succ, Finset.sum_range_zero, romikQ_1, romikQ_2, romikQ_3, Nat.reduceAdd, Nat.reduceMul,
    Nat.reduceSub, ch_4_2, ch_6_2, ch_6_4, ch_8_2, ch_8_4, ch_8_6, ch_10_2, ch_10_4, ch_10_6, ch_10_8, ch_12_2, ch_12_4, ch_12_6, ch_12_8, ch_12_10, ch_14_2, ch_14_4, ch_14_6, ch_14_8, ch_14_10, ch_14_12, ch_16_2, ch_16_4, ch_16_6, ch_16_8, ch_16_10, ch_16_12, ch_16_14, ch_18_2, ch_18_4, ch_18_6, ch_18_8, ch_18_10, ch_18_12, ch_18_14, ch_18_16, ch_20_2, ch_20_4, ch_20_6, ch_20_8, ch_20_10, ch_20_12, ch_20_14, ch_20_16, ch_20_18]
  norm_num

theorem romikQ_5 : romikQ 5 = 1399055625 := by
  rw [romikQ_rec 5 (by norm_num)]
  simp only [Pi3, Finset.prod_range_succ, Finset.prod_range_zero, Finset.sum_Ico_eq_sum_range,
    Finset.sum_range_succ, Finset.sum_range_zero, romikQ_1, romikQ_2, romikQ_3, romikQ_4, Nat.reduceAdd, Nat.reduceMul,
    Nat.reduceSub, ch_4_2, ch_6_2, ch_6_4, ch_8_2, ch_8_4, ch_8_6, ch_10_2, ch_10_4, ch_10_6, ch_10_8, ch_12_2, ch_12_4, ch_12_6, ch_12_8, ch_12_10, ch_14_2, ch_14_4, ch_14_6, ch_14_8, ch_14_10, ch_14_12, ch_16_2, ch_16_4, ch_16_6, ch_16_8, ch_16_10, ch_16_12, ch_16_14, ch_18_2, ch_18_4, ch_18_6, ch_18_8, ch_18_10, ch_18_12, ch_18_14, ch_18_16, ch_20_2, ch_20_4, ch_20_6, ch_20_8, ch_20_10, ch_20_12, ch_20_14, ch_20_16, ch_20_18]
  norm_num

theorem romikQ_6 : romikQ 6 = 1221037941375 := by
  rw [romikQ_rec 6 (by norm_num)]
  simp only [Pi3, Finset.prod_range_succ, Finset.prod_range_zero, Finset.sum_Ico_eq_sum_range,
    Finset.sum_range_succ, Finset.sum_range_zero, romikQ_1, romikQ_2, romikQ_3, romikQ_4, romikQ_5, Nat.reduceAdd, Nat.reduceMul,
    Nat.reduceSub, ch_4_2, ch_6_2, ch_6_4, ch_8_2, ch_8_4, ch_8_6, ch_10_2, ch_10_4, ch_10_6, ch_10_8, ch_12_2, ch_12_4, ch_12_6, ch_12_8, ch_12_10, ch_14_2, ch_14_4, ch_14_6, ch_14_8, ch_14_10, ch_14_12, ch_16_2, ch_16_4, ch_16_6, ch_16_8, ch_16_10, ch_16_12, ch_16_14, ch_18_2, ch_18_4, ch_18_6, ch_18_8, ch_18_10, ch_18_12, ch_18_14, ch_18_16, ch_20_2, ch_20_4, ch_20_6, ch_20_8, ch_20_10, ch_20_12, ch_20_14, ch_20_16, ch_20_18]
  norm_num

theorem romikQ_7 : romikQ 7 = 1513229875486875 := by
  rw [romikQ_rec 7 (by norm_num)]
  simp only [Pi3, Finset.prod_range_succ, Finset.prod_range_zero, Finset.sum_Ico_eq_sum_range,
    Finset.sum_range_succ, Finset.sum_range_zero, romikQ_1, romikQ_2, romikQ_3, romikQ_4, romikQ_5, romikQ_6, Nat.reduceAdd, Nat.reduceMul,
    Nat.reduceSub, ch_4_2, ch_6_2, ch_6_4, ch_8_2, ch_8_4, ch_8_6, ch_10_2, ch_10_4, ch_10_6, ch_10_8, ch_12_2, ch_12_4, ch_12_6, ch_12_8, ch_12_10, ch_14_2, ch_14_4, ch_14_6, ch_14_8, ch_14_10, ch_14_12, ch_16_2, ch_16_4, ch_16_6, ch_16_8, ch_16_10, ch_16_12, ch_16_14, ch_18_2, ch_18_4, ch_18_6, ch_18_8, ch_18_10, ch_18_12, ch_18_14, ch_18_16, ch_20_2, ch_20_4, ch_20_6, ch_20_8, ch_20_10, ch_20_12, ch_20_14, ch_20_16, ch_20_18]
  norm_num

theorem romikQ_8 : romikQ 8 = 2526879997358510625 := by
  rw [romikQ_rec 8 (by norm_num)]
  simp only [Pi3, Finset.prod_range_succ, Finset.prod_range_zero, Finset.sum_Ico_eq_sum_range,
    Finset.sum_range_succ, Finset.sum_range_zero, romikQ_1, romikQ_2, romikQ_3, romikQ_4, romikQ_5, romikQ_6, romikQ_7, Nat.reduceAdd, Nat.reduceMul,
    Nat.reduceSub, ch_4_2, ch_6_2, ch_6_4, ch_8_2, ch_8_4, ch_8_6, ch_10_2, ch_10_4, ch_10_6, ch_10_8, ch_12_2, ch_12_4, ch_12_6, ch_12_8, ch_12_10, ch_14_2, ch_14_4, ch_14_6, ch_14_8, ch_14_10, ch_14_12, ch_16_2, ch_16_4, ch_16_6, ch_16_8, ch_16_10, ch_16_12, ch_16_14, ch_18_2, ch_18_4, ch_18_6, ch_18_8, ch_18_10, ch_18_12, ch_18_14, ch_18_16, ch_20_2, ch_20_4, ch_20_6, ch_20_8, ch_20_10, ch_20_12, ch_20_14, ch_20_16, ch_20_18]
  norm_num

theorem romikQ_9 : romikQ 9 = 5469272714829657020625 := by
  rw [romikQ_rec 9 (by norm_num)]
  simp only [Pi3, Finset.prod_range_succ, Finset.prod_range_zero, Finset.sum_Ico_eq_sum_range,
    Finset.sum_range_succ, Finset.sum_range_zero, romikQ_1, romikQ_2, romikQ_3, romikQ_4, romikQ_5, romikQ_6, romikQ_7, romikQ_8, Nat.reduceAdd, Nat.reduceMul,
    Nat.reduceSub, ch_4_2, ch_6_2, ch_6_4, ch_8_2, ch_8_4, ch_8_6, ch_10_2, ch_10_4, ch_10_6, ch_10_8, ch_12_2, ch_12_4, ch_12_6, ch_12_8, ch_12_10, ch_14_2, ch_14_4, ch_14_6, ch_14_8, ch_14_10, ch_14_12, ch_16_2, ch_16_4, ch_16_6, ch_16_8, ch_16_10, ch_16_12, ch_16_14, ch_18_2, ch_18_4, ch_18_6, ch_18_8, ch_18_10, ch_18_12, ch_18_14, ch_18_16, ch_20_2, ch_20_4, ch_20_6, ch_20_8, ch_20_10, ch_20_12, ch_20_14, ch_20_16, ch_20_18]
  norm_num

theorem romikQ_10 : romikQ 10 = 14892997153152592003359375 := by
  rw [romikQ_rec 10 (by norm_num)]
  simp only [Pi3, Finset.prod_range_succ, Finset.prod_range_zero, Finset.sum_Ico_eq_sum_range,
    Finset.sum_range_succ, Finset.sum_range_zero, romikQ_1, romikQ_2, romikQ_3, romikQ_4, romikQ_5, romikQ_6, romikQ_7, romikQ_8, romikQ_9, Nat.reduceAdd, Nat.reduceMul,
    Nat.reduceSub, ch_4_2, ch_6_2, ch_6_4, ch_8_2, ch_8_4, ch_8_6, ch_10_2, ch_10_4, ch_10_6, ch_10_8, ch_12_2, ch_12_4, ch_12_6, ch_12_8, ch_12_10, ch_14_2, ch_14_4, ch_14_6, ch_14_8, ch_14_10, ch_14_12, ch_16_2, ch_16_4, ch_16_6, ch_16_8, ch_16_10, ch_16_12, ch_16_14, ch_18_2, ch_18_4, ch_18_6, ch_18_8, ch_18_10, ch_18_12, ch_18_14, ch_18_16, ch_20_2, ch_20_4, ch_20_6, ch_20_8, ch_20_10, ch_20_12, ch_20_14, ch_20_16, ch_20_18]
  norm_num

theorem romikV_eq_of_romikQ {n : ℕ} {z : ℤ} (h : romikQ n = z) : romikV n = z := by
  have := romikV_spec n
  rw [h] at this
  exact_mod_cast this.symm

/-- Sanity guard: the source's eleven printed values of `v(n)`, `n = 0, …, 10`. -/
theorem romikV_printed_values :
    (List.range 11).map romikV = [1, 1, 47, 7395, 2453425, 1399055625, 1221037941375, 1513229875486875, 2526879997358510625, 5469272714829657020625, 14892997153152592003359375] := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil]
  rw [romikV_eq_of_romikQ (z := 1) (by simp [romikQ_zero])]
  rw [romikV_eq_of_romikQ (z := 1) (by rw [romikQ_1]; norm_num)]
  rw [romikV_eq_of_romikQ (z := 47) (by rw [romikQ_2]; norm_num)]
  rw [romikV_eq_of_romikQ (z := 7395) (by rw [romikQ_3]; norm_num)]
  rw [romikV_eq_of_romikQ (z := 2453425) (by rw [romikQ_4]; norm_num)]
  rw [romikV_eq_of_romikQ (z := 1399055625) (by rw [romikQ_5]; norm_num)]
  rw [romikV_eq_of_romikQ (z := 1221037941375) (by rw [romikQ_6]; norm_num)]
  rw [romikV_eq_of_romikQ (z := 1513229875486875) (by rw [romikQ_7]; norm_num)]
  rw [romikV_eq_of_romikQ (z := 2526879997358510625) (by rw [romikQ_8]; norm_num)]
  rw [romikV_eq_of_romikQ (z := 5469272714829657020625) (by rw [romikQ_9]; norm_num)]
  rw [romikV_eq_of_romikQ (z := 14892997153152592003359375) (by rw [romikQ_10]; norm_num)]

/-- Sanity guard: `v(10)` is not divisible by `3^4` (the exception `(p,e) = (3,4)`, `n = 10`). -/
theorem romikV_10_not_dvd : ¬ (3 : ℤ) ^ 4 ∣ romikV 10 := by
  rw [romikV_eq_of_romikQ romikQ_10]
  decide
```

### `RomikPint.lean`

```lean
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# `p`-integral rationals and their reduction modulo `p`

`Pint p q` means `p ∤ den q`.  On such rationals the cast `ℚ → ZMod p` is additive and
multiplicative.  We also record the bridges between `Pint` and divisibility of integers.
-/

open Finset

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-- `q` is `p`-integral. -/
def Pint (p : ℕ) (q : ℚ) : Prop := ¬ p ∣ q.den

namespace Pint

variable {p : ℕ} [hp : Fact p.Prime] {q r : ℚ}

theorem iff_cast : Pint p q ↔ ((q.den : ℕ) : ZMod p) ≠ 0 := by
  rw [Pint, Ne, ZMod.natCast_eq_zero_iff]

theorem add (hq : Pint p q) (hr : Pint p r) : Pint p (q + r) := fun h =>
  ((Nat.Prime.dvd_mul hp.out).1 (h.trans (Rat.add_den_dvd q r))).elim hq hr

theorem mul (hq : Pint p q) (hr : Pint p r) : Pint p (q * r) := fun h =>
  ((Nat.Prime.dvd_mul hp.out).1 (h.trans (Rat.mul_den_dvd q r))).elim hq hr

theorem neg (hq : Pint p q) : Pint p (-q) := by
  unfold Pint; rw [Rat.neg_den]; exact hq

theorem sub (hq : Pint p q) (hr : Pint p r) : Pint p (q - r) := by
  rw [sub_eq_add_neg]; exact hq.add hr.neg

theorem intCast (z : ℤ) : Pint p (z : ℚ) := by
  unfold Pint; rw [Rat.den_intCast]; exact hp.out.not_dvd_one

theorem natCast (n : ℕ) : Pint p (n : ℚ) := by
  have := intCast (p := p) (n : ℤ); exact_mod_cast this

theorem one : Pint p 1 := by exact_mod_cast natCast (p := p) 1

theorem zero : Pint p 0 := by exact_mod_cast natCast (p := p) 0

theorem pow (hq : Pint p q) (k : ℕ) : Pint p (q ^ k) := by
  induction k with
  | zero => simpa using one
  | succ k ih => rw [pow_succ]; exact ih.mul hq

theorem inv_nat {n : ℕ} (hn : ¬ p ∣ n) : Pint p ((n : ℚ)⁻¹) := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero p)
  unfold Pint
  rw [Rat.inv_natCast_den]
  simpa [hn0] using hn

theorem div_nat (hq : Pint p q) {n : ℕ} (hn : ¬ p ∣ n) : Pint p (q / n) := by
  rw [div_eq_mul_inv]; exact hq.mul (inv_nat hn)

theorem sum {ι : Type*} (s : Finset ι) (g : ι → ℚ) (h : ∀ i ∈ s, Pint p (g i)) :
    Pint p (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

end Pint

namespace Pint

variable {p : ℕ} [hp : Fact p.Prime] {q r : ℚ}

theorem cast_add (hq : Pint p q) (hr : Pint p r) : ((q + r : ℚ) : ZMod p) = q + r :=
  Rat.cast_add_of_ne_zero (iff_cast.1 hq) (iff_cast.1 hr)

theorem cast_mul (hq : Pint p q) (hr : Pint p r) : ((q * r : ℚ) : ZMod p) = q * r :=
  Rat.cast_mul_of_ne_zero (iff_cast.1 hq) (iff_cast.1 hr)

theorem cast_neg (q : ℚ) : ((-q : ℚ) : ZMod p) = -q := Rat.cast_neg q

theorem cast_sub (hq : Pint p q) (hr : Pint p r) : ((q - r : ℚ) : ZMod p) = q - r := by
  rw [sub_eq_add_neg, cast_add hq hr.neg, cast_neg, sub_eq_add_neg]

theorem cast_sum {ι : Type*} (s : Finset ι) (g : ι → ℚ) (h : ∀ i ∈ s, Pint p (g i)) :
    ((∑ i ∈ s, g i : ℚ) : ZMod p) = ∑ i ∈ s, (g i : ZMod p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      cast_add (h a (Finset.mem_insert_self a s))
        (sum s g (fun i hi => h i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi))]

theorem cast_pow (hq : Pint p q) (k : ℕ) : ((q ^ k : ℚ) : ZMod p) = (q : ZMod p) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, cast_mul (hq.pow k) hq, ih, pow_succ]

theorem cast_inv_nat {n : ℕ} (hn : ¬ p ∣ n) :
    (((n : ℚ)⁻¹ : ℚ) : ZMod p) = ((n : ZMod p))⁻¹ := by
  have hn0 : (n : ℚ) ≠ 0 := by
    have : n ≠ 0 := by rintro rfl; exact hn (dvd_zero p)
    exact_mod_cast this
  have h1 : (((n : ℚ)⁻¹ * n : ℚ) : ZMod p) = 1 := by rw [inv_mul_cancel₀ hn0]; simp
  rw [cast_mul (inv_nat hn) (natCast n), Rat.cast_natCast] at h1
  exact eq_inv_of_mul_eq_one_left h1

theorem cast_div_nat (hq : Pint p q) {n : ℕ} (hn : ¬ p ∣ n) :
    ((q / n : ℚ) : ZMod p) = (q : ZMod p) / (n : ZMod p) := by
  rw [div_eq_mul_inv, cast_mul hq (inv_nat hn), cast_inv_nat hn, div_eq_mul_inv]

/-- If a `p`-integral `q` reduces to `0`, then `q / p` is still `p`-integral. -/
theorem div_p_of_cast_eq_zero (hq : Pint p q) (h : (q : ZMod p) = 0) : Pint p (q / p) := by
  have hden := iff_cast.1 hq
  rw [Rat.cast_def] at h
  have hnum : ((q.num : ℤ) : ZMod p) = 0 := by
    rcases mul_eq_zero.1 (show ((q.num : ZMod p)) * ((q.den : ZMod p))⁻¹ = 0 from h) with h1 | h1
    · exact h1
    · exact absurd (inv_eq_zero.1 h1) hden
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hnum
  obtain ⟨k, hk⟩ := hnum
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have : q / p = (k : ℚ) / (q.den : ℕ) := by
    conv_lhs => rw [← Rat.num_div_den q]
    rw [hk]; push_cast; field_simp
  rw [this]
  exact (intCast k).div_nat hq

/-- If `q / p` is `p`-integral then `q` reduces to `0`. -/
theorem cast_eq_zero_of_div_p (h : Pint p (q / p)) : (q : ZMod p) = 0 := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have : q = (p : ℚ) * (q / p) := by field_simp
  rw [this, cast_mul (natCast p) h, Rat.cast_natCast, ZMod.natCast_self, zero_mul]

/-- An integer `z` with `z / p^e` `p`-integral is divisible by `p^e`. -/
theorem int_dvd (z : ℤ) (e : ℕ) (h : Pint p ((z : ℚ) / (p : ℚ) ^ e)) : (p : ℤ) ^ e ∣ z := by
  set w : ℚ := (z : ℚ) / (p : ℚ) ^ e with hw
  have hpe : ((p : ℚ) ^ e) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have h1 : (w.num : ℚ) * (p : ℚ) ^ e = (z : ℚ) * (w.den : ℚ) := by
    rw [← Rat.mul_den_eq_num, hw]; field_simp
  have h2 : w.num * (p : ℤ) ^ e = z * (w.den : ℤ) := by exact_mod_cast h1
  -- `den ∣ num * p^e`, coprime to `num`, hence `den ∣ p^e`, coprime to `p`: `den = 1`.
  have h3 : w.den ∣ p ^ e * w.num.natAbs := by
    refine ⟨z.natAbs, ?_⟩
    have := congrArg Int.natAbs h2
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast,
      Int.natAbs_natCast] at this
    rw [mul_comm (p ^ e), this, mul_comm]
  have h5 : w.den ∣ p ^ e := Nat.Coprime.dvd_of_dvd_mul_right (Nat.coprime_comm.1 w.reduced) h3
  have h6 : Nat.Coprime w.den (p ^ e) :=
    Nat.Coprime.pow_right e ((Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 h))
  have h7 : w.den = 1 := Nat.Coprime.eq_one_of_dvd h6 h5
  rw [h7, Nat.cast_one, mul_one] at h2
  exact ⟨w.num, by rw [← h2, mul_comm]⟩

/-- Decomposition `n = p^ν · u` with `ν = padicValNat p n` and `p ∤ u`. -/
theorem nat_decomp {n : ℕ} (hn : n ≠ 0) :
    ∃ u : ℕ, ¬ p ∣ u ∧ n = p ^ padicValNat p n * u := by
  refine ⟨ordCompl[p] n, Nat.not_dvd_ordCompl hp.out hn, ?_⟩
  rw [← Nat.factorization_def n hp.out]
  exact (Nat.ordProj_mul_ordCompl_eq_self n p).symm

/-- If `ν_p(Y) ≤ ν_p(X) + k` then `p^k X / Y` is `p`-integral. -/
theorem of_val_le {X Y k : ℕ} (hX : X ≠ 0) (hY : Y ≠ 0)
    (h : padicValNat p Y ≤ padicValNat p X + k) :
    Pint p ((p : ℚ) ^ k * X / Y) := by
  obtain ⟨uX, -, hXe⟩ := nat_decomp (p := p) hX
  obtain ⟨uY, huY, hYe⟩ := nat_decomp (p := p) hY
  set vX := padicValNat p X
  set vY := padicValNat p Y
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have huY0 : (uY : ℚ) ≠ 0 := by
    have : uY ≠ 0 := by rintro rfl; exact huY (dvd_zero p)
    exact_mod_cast this
  have hpY : ((p : ℚ) ^ vY) ≠ 0 := pow_ne_zero _ hp0
  have hpow : (p : ℚ) ^ k * (p : ℚ) ^ vX = (p : ℚ) ^ (vX + k - vY) * (p : ℚ) ^ vY := by
    rw [← pow_add, ← pow_add, Nat.sub_add_cancel h, add_comm]
  have : (p : ℚ) ^ k * X / Y = ((p ^ (vX + k - vY) * uX : ℕ) : ℚ) / (uY : ℕ) := by
    rw [hXe, hYe]
    push_cast
    rw [div_eq_div_iff (mul_ne_zero hpY huY0) huY0]
    linear_combination (↑uX * ↑uY : ℚ) * hpow
  rw [this]
  exact (natCast _).div_nat huY

/-- If `ν_p(Y) + 1 ≤ ν_p(X) + k` then `p^k X / Y` reduces to `0`. -/
theorem cast_eq_zero_of_val_lt {X Y k : ℕ} (hX : X ≠ 0) (hY : Y ≠ 0)
    (h : padicValNat p Y + 1 ≤ padicValNat p X + k) :
    (((p : ℚ) ^ k * X / Y : ℚ) : ZMod p) = 0 := by
  apply cast_eq_zero_of_div_p
  have hpY : p * Y ≠ 0 := Nat.mul_ne_zero hp.out.ne_zero hY
  have hv : padicValNat p (p * Y) = padicValNat p Y + 1 := by
    rw [padicValNat.mul hp.out.ne_zero hY, padicValNat_self, add_comm]
  have := of_val_le (p := p) hX hpY (by rw [hv]; exact h)
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  convert this using 1
  push_cast
  field_simp

end Pint
```

### `RomikWeight.lean`

```lean
import RomikDefs
import RomikPint
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Tactic.IntervalCases

/-!
# The weight bound for `f_j = Π₃(j)/(2j)!`

For a prime `p ≡ 3 (mod 4)` and `p^(2B+1) > 2j` we prove `ν_p((2j)!) ≤ ν_p(Π₃(j)) + B`
(Legendre-type counting, one prime power `p^s` at a time: odd `s` contribute at least `-1`,
even `s` at least `0`, and `p^s > 2j` contributes `0`).  With `a = (p+1)/2` this gives
`ν_p((2j)!) ≤ ν_p(Π₃(j)) + j/a` for all `j`, and one better when `j ≥ 2a`.
-/

open Finset

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-- `A₄(j) = ∏_{i<j} (4i+1) = ∏_{i=1}^{j} (4i-3)`. -/
def A4 (j : ℕ) : ℕ := ∏ i ∈ range j, (4 * i + 1)

theorem Pi3_eq_sq (j : ℕ) : Pi3 j = A4 j ^ 2 := by
  unfold Pi3 A4
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  congr 1

theorem A4_pos (j : ℕ) : 0 < A4 j := Finset.prod_pos (fun i _ => by omega)

theorem Pi3_pos (j : ℕ) : 0 < Pi3 j := by rw [Pi3_eq_sq]; exact pow_pos (A4_pos j) 2

namespace RomikWeight

variable {p : ℕ} [hp : Fact p.Prime]

theorem val_eq_card {n L : ℕ} (hn : 0 < n) (hL : n < p ^ L) :
    padicValNat p n = #{s ∈ Ico 1 L | p ^ s ∣ n} := by
  have h1 := Nat.emultiplicity_eq_card_pow_dvd (m := p) (n := n) (b := L) hp.out.ne_one hn
    (Nat.log_lt_of_lt_pow hn.ne' hL)
  have h2 := padicValNat_eq_emultiplicity (p := p) hn.ne'
  rw [h1] at h2
  exact_mod_cast h2

theorem val_prod (x : ℕ → ℕ) (hx : ∀ i, 0 < x i) (j : ℕ) :
    padicValNat p (∏ i ∈ range j, x i) = ∑ i ∈ range j, padicValNat p (x i) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [prod_range_succ, sum_range_succ,
      padicValNat.mul (Finset.prod_pos (fun i _ => hx i)).ne' (hx j).ne', ih]

theorem val_A4 (j L : ℕ) (hL : 4 * j < p ^ L) :
    padicValNat p (A4 j) = ∑ s ∈ Ico 1 L, #{i ∈ range j | p ^ s ∣ 4 * i + 1} := by
  rw [A4, val_prod _ (fun i => by omega)]
  rw [Finset.sum_congr rfl (fun i hi => val_eq_card (p := p) (L := L) (n := 4 * i + 1)
    (by omega) (by rw [Finset.mem_range] at hi; omega))]
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]

theorem cong_iff {P v : ℕ} (hP : Nat.Coprime P 4) (hv : P ∣ 4 * v + 1) (i : ℕ) :
    P ∣ 4 * i + 1 ↔ i ≡ v [MOD P] := by
  constructor
  · intro h
    have h1 : 4 * i + 1 ≡ 4 * v + 1 [MOD P] :=
      (Nat.modEq_zero_iff_dvd.2 h).trans (Nat.modEq_zero_iff_dvd.2 hv).symm
    exact Nat.ModEq.cancel_left_of_coprime (c := 4) hP (Nat.ModEq.add_right_cancel' 1 h1)
  · intro h
    have h1 : 4 * i + 1 ≡ 4 * v + 1 [MOD P] := (h.mul_left 4).add_right 1
    exact Nat.modEq_zero_iff_dvd.1 (h1.trans (Nat.modEq_zero_iff_dvd.2 hv))

theorem count_eq {P v : ℕ} (hP0 : 0 < P) (hP : Nat.Coprime P 4) (hv : P ∣ 4 * v + 1)
    (hvP : v < P) (j : ℕ) :
    #{i ∈ range j | P ∣ 4 * i + 1} = j / P + if v < j % P then 1 else 0 := by
  have h1 : #{i ∈ range j | P ∣ 4 * i + 1} = Nat.count (· ≡ v [MOD P]) j := by
    rw [Nat.count_eq_card_filter_range]
    congr 1
    exact Finset.filter_congr (fun i _ => cong_iff hP hv i)
  rw [h1, Nat.count_modEq_card j hP0 v, Nat.mod_eq_of_lt hvP]

theorem coprime_pow_four (hp4 : p % 4 = 3) (s : ℕ) : Nat.Coprime (p ^ s) 4 := by
  apply Nat.Coprime.pow_left
  rw [Nat.Prime.coprime_iff_not_dvd hp.out]
  intro h
  have := Nat.le_of_dvd (by norm_num) h
  interval_cases p <;> simp_all

theorem pow_mod_four (hp4 : p % 4 = 3) (s : ℕ) : p ^ s % 4 = if Even s then 1 else 3 := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ, Nat.mul_mod, ih, hp4]
    by_cases hs : Even s
    · have : ¬ Even (s + 1) := by rw [Nat.even_add_one]; exact not_not.2 hs
      simp [hs, this]
    · have : Even (s + 1) := by rw [Nat.even_add_one]; exact hs
      simp [hs, this]

theorem two_div (P j : ℕ) (hP : 0 < P) :
    2 * j / P = 2 * (j / P) + 2 * (j % P) / P ∧ 2 * (j % P) / P ≤ 1 ∧
      (2 * (j % P) < P → 2 * (j % P) / P = 0) := by
  have hdm := Nat.div_add_mod j P
  have hml := Nat.mod_lt j hP
  refine ⟨?_, ?_, fun h => Nat.div_eq_of_lt h⟩
  · have : 2 * j = 2 * (j % P) + P * (2 * (j / P)) := by
      nth_rewrite 1 [← hdm]; ring
    rw [this, Nat.add_mul_div_left _ _ hP]; ring
  · have : 2 * (j % P) / P < 2 := by
      rw [Nat.div_lt_iff_lt_mul hP]; omega
    omega

/-- Exact count, with an explicit residue `v`. -/
theorem count_pow (hp4 : p % 4 = 3) (s j : ℕ) :
    #{i ∈ range j | p ^ s ∣ 4 * i + 1} =
      j / p ^ s + if (if Even s then (p ^ s - 1) / 4 else (3 * p ^ s - 1) / 4) < j % p ^ s
        then 1 else 0 := by
  have hP0 : 0 < p ^ s := pow_pos hp.out.pos s
  have hcop := coprime_pow_four hp4 s
  have hm := pow_mod_four hp4 s
  by_cases hs : Even s
  · simp only [hs, ↓reduceIte] at hm ⊢
    exact count_eq hP0 hcop ⟨1, by omega⟩ (by omega) j
  · simp only [hs, ↓reduceIte] at hm ⊢
    exact count_eq hP0 hcop ⟨3, by omega⟩ (by omega) j

/-- Each prime power contributes at least `-1`. -/
theorem term_ge (hp4 : p % 4 = 3) (s j : ℕ) :
    2 * j / p ^ s ≤ 2 * #{i ∈ range j | p ^ s ∣ 4 * i + 1} + 1 := by
  rw [count_pow hp4 s j]
  have hP0 : 0 < p ^ s := pow_pos hp.out.pos s
  obtain ⟨h1, h2, -⟩ := two_div (p ^ s) j hP0
  split_ifs <;> omega

/-- Even prime powers contribute at least `0`. -/
theorem term_ge_even (hp4 : p % 4 = 3) (s j : ℕ) (hs : Even s) :
    2 * j / p ^ s ≤ 2 * #{i ∈ range j | p ^ s ∣ 4 * i + 1} := by
  rw [count_pow hp4 s j]
  simp only [hs, ↓reduceIte]
  have hP0 : 0 < p ^ s := pow_pos hp.out.pos s
  have hm := pow_mod_four hp4 s
  simp only [hs, ↓reduceIte] at hm
  obtain ⟨h1, h2, h3⟩ := two_div (p ^ s) j hP0
  have hml := Nat.mod_lt j hP0
  by_cases h4 : p ^ s ≤ 2 * (j % p ^ s)
  · have hv : (p ^ s - 1) / 4 < j % p ^ s := by omega
    simp only [hv, ↓reduceIte]
    omega
  · have := h3 (by omega)
    split_ifs <;> omega

/-- Prime powers above `2j` contribute nothing. -/
theorem term_big (s j : ℕ) (h : 2 * j < p ^ s) : 2 * j / p ^ s = 0 := Nat.div_eq_of_lt h

/-- **Weight bound.** If `2j < p^(2B+1)` then `ν_p((2j)!) ≤ ν_p(Π₃(j)) + B`. -/
theorem weight (hp4 : p % 4 = 3) (j B : ℕ) (hB : 2 * j < p ^ (2 * B + 1)) :
    padicValNat p (2 * j).factorial ≤ padicValNat p (Pi3 j) + B := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  have hp1 : 1 < p := hp.out.one_lt
  set L := 4 * j + 1
  have hL : 4 * j < p ^ L := lt_trans (Nat.lt_succ_self _) (Nat.lt_pow_self hp1)
  have hL2 : Nat.log p (2 * j) < L :=
    Nat.log_lt_of_lt_pow (by omega) (lt_of_le_of_lt (by omega) hL)
  rw [padicValNat_factorial hL2, Pi3_eq_sq, padicValNat.pow (p := p) (A4 j) 2, val_A4 j L hL,
    Finset.mul_sum]
  -- termwise bound with an indicator of "odd `s` with `p^s ≤ 2j`"
  have hterm : ∀ s ∈ Ico 1 L, 2 * j / p ^ s ≤
      2 * #{i ∈ range j | p ^ s ∣ 4 * i + 1} + (if ¬ Even s ∧ p ^ s ≤ 2 * j then 1 else 0) := by
    intro s _
    by_cases hbig : 2 * j < p ^ s
    · rw [term_big s j hbig]; exact Nat.zero_le _
    by_cases hs : Even s
    · have := term_ge_even hp4 s j hs
      omega
    · have := term_ge hp4 s j
      have hc : ¬ Even s ∧ p ^ s ≤ 2 * j := ⟨hs, by omega⟩
      simp only [hc, ↓reduceIte]
      exact this
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, ← Finset.card_filter]
  gcongr
  -- the odd `s` with `p^s ≤ 2j` are among `1, 3, …, 2B-1`
  calc #{s ∈ Ico 1 L | ¬ Even s ∧ p ^ s ≤ 2 * j}
      ≤ #((range B).image (fun i => 2 * i + 1)) := by
        apply Finset.card_le_card
        intro s hs
        rw [Finset.mem_filter, Finset.mem_Ico] at hs
        obtain ⟨⟨hs1, -⟩, hodd, hle⟩ := hs
        rw [Nat.not_even_iff_odd] at hodd
        obtain ⟨i, rfl⟩ := hodd
        rw [Finset.mem_image]
        refine ⟨i, ?_, rfl⟩
        rw [Finset.mem_range]
        have : p ^ (2 * i + 1) < p ^ (2 * B + 1) := lt_of_le_of_lt hle hB
        rw [Nat.pow_lt_pow_iff_right (by omega)] at this
        omega
    _ ≤ #(range B) := Finset.card_image_le
    _ = B := Finset.card_range B

theorem pow_bound (hp3 : 3 ≤ p) (B : ℕ) (hB : 1 ≤ B) : (p + 1) * (B + 2) ≤ p ^ (2 * B + 1) := by
  induction B, hB using Nat.le_induction with
  | base =>
    have h1 : 3 * p ≤ p * p := Nat.mul_le_mul_right p hp3
    have h2 : 3 * (p * p) ≤ p * (p * p) := Nat.mul_le_mul_right (p * p) hp3
    have : p ^ (2 * 1 + 1) = p * (p * p) := by ring
    rw [this]; nlinarith
  | succ B hB ih =>
    rw [show 2 * (B + 1) + 1 = (2 * B + 1) + 2 by ring, pow_add]
    have h9 : 9 ≤ p ^ 2 := by nlinarith
    calc (p + 1) * (B + 1 + 2) ≤ (p + 1) * (B + 2) * 9 := by nlinarith
      _ ≤ p ^ (2 * B + 1) * p ^ 2 := Nat.mul_le_mul ih h9

/-- `ν_p((2j)!) ≤ ν_p(Π₃(j)) + ⌊j/a⌋`, `a = (p+1)/2`. -/
theorem weight_K (hp4 : p % 4 = 3) (j : ℕ) :
    padicValNat p (2 * j).factorial ≤ padicValNat p (Pi3 j) + j / ((p + 1) / 2) := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have ha : 2 * ((p + 1) / 2) = p + 1 := by omega
  have ha0 : 0 < (p + 1) / 2 := by omega
  apply weight hp4
  have hlt := Nat.lt_mul_div_succ j ha0
  rcases Nat.eq_zero_or_pos (j / ((p + 1) / 2)) with h0 | h1
  · rw [h0] at hlt ⊢; simp; omega
  · have := pow_bound hp3 _ h1
    nlinarith

/-- For `j ≥ 2a`: `ν_p((2j)!) + 1 ≤ ν_p(Π₃(j)) + ⌊j/a⌋`. -/
theorem weight_K_strict (hp4 : p % 4 = 3) (j : ℕ) (hj : 2 * ((p + 1) / 2) ≤ j) :
    padicValNat p (2 * j).factorial + 1 ≤ padicValNat p (Pi3 j) + j / ((p + 1) / 2) := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have ha : 2 * ((p + 1) / 2) = p + 1 := by omega
  have ha0 : 0 < (p + 1) / 2 := by omega
  have hK : 2 ≤ j / ((p + 1) / 2) := (Nat.le_div_iff_mul_le ha0).2 (by linarith)
  have hlt := Nat.lt_mul_div_succ j ha0
  have := pow_bound hp3 (j / ((p + 1) / 2) - 1) (by omega)
  have hw := weight hp4 j (j / ((p + 1) / 2) - 1) (by
    rw [show j / ((p + 1) / 2) - 1 + 2 = j / ((p + 1) / 2) + 1 by omega] at this
    nlinarith)
  omega

end RomikWeight
```

### `RomikNorm.lean`

```lean
import RomikWeight
import Mathlib.Data.Nat.Choose.Basic

/-!
# The square-root coefficients and their normalised residues

`cQ n = romikQ n / (2^n (2n)!)` and `fQ j = Π₃(j)/(2j)!`.  Recurrence (2.6) is equivalent to
`2 cQ n + Σ_{m=1}^{n-1} cQ m cQ (n-m) = fQ n` (`n ≥ 1`), i.e. `cQ` is the square root of
`Σ fQ j t^j` (source (2.5)).  With `a = (p+1)/2`, `dd n = p^(n/a) cQ n` is `p`-integral, and its
reduction `D n` satisfies the *no-carry* convolution recurrence `noCarry_rec`.
-/

open Finset

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Romik

noncomputable def fQ (j : ℕ) : ℚ := (Pi3 j : ℚ) / ((2 * j).factorial : ℚ)

noncomputable def cQ (n : ℕ) : ℚ := romikQ n / (2 ^ n * ((2 * n).factorial : ℚ))

theorem cQ_zero : cQ 0 = 1 := by simp [cQ, romikQ_zero]

theorem fQ_zero : fQ 0 = 1 := by simp [fQ, Pi3]

theorem romikQ_eq (n : ℕ) : romikQ n = 2 ^ n * ((2 * n).factorial : ℚ) * cQ n := by
  unfold cQ
  have : (2 : ℚ) ^ n * ((2 * n).factorial : ℚ) ≠ 0 := by positivity
  field_simp

theorem conv_term (n m : ℕ) (hm : m ≤ n) :
    ((Nat.choose (2 * n) (2 * m) : ℕ) : ℚ) * romikQ m * romikQ (n - m) =
      2 ^ n * ((2 * n).factorial : ℚ) * (cQ m * cQ (n - m)) := by
  rw [romikQ_eq m, romikQ_eq (n - m)]
  have hc := Nat.choose_mul_factorial_mul_factorial (show 2 * m ≤ 2 * n by omega)
  have h2 : 2 * n - 2 * m = 2 * (n - m) := by omega
  rw [h2] at hc
  have hc' : ((Nat.choose (2 * n) (2 * m) : ℕ) : ℚ) * ((2 * m).factorial : ℚ) *
      ((2 * (n - m)).factorial : ℚ) = ((2 * n).factorial : ℚ) := by exact_mod_cast hc
  have hp : (2 : ℚ) ^ n = 2 ^ m * 2 ^ (n - m) := by rw [← pow_add]; congr 1; omega
  rw [← hc', hp]
  ring

/-- (2.6) divided by `2^n (2n)!`. -/
theorem conv (n : ℕ) (hn : 1 ≤ n) :
    2 * cQ n + ∑ m ∈ Ico 1 n, cQ m * cQ (n - m) = fQ n := by
  have hr := romikQ_rec n hn
  rw [Finset.sum_congr rfl (fun m hm => conv_term n m (by rw [Finset.mem_Ico] at hm; omega))]
    at hr
  rw [← Finset.mul_sum, romikQ_eq n] at hr
  have hpos : (2 : ℚ) ^ n * ((2 * n).factorial : ℚ) ≠ 0 := by positivity
  have h2 : (2 : ℚ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hf : ((2 * n).factorial : ℚ) ≠ 0 := by positivity
  have h2' : (2 : ℚ) ^ (n - 1) ≠ 0 := by positivity
  rw [h2] at hr
  have := hr
  field_simp at this
  unfold fQ
  rw [eq_div_iff hf]
  linear_combination this

/-- The recursive form. -/
theorem cQ_rec (n : ℕ) (hn : 1 ≤ n) :
    cQ n = (fQ n - ∑ m ∈ Ico 1 n, cQ m * cQ (n - m)) / 2 := by
  have := conv n hn
  linarith

/-- Carry lemma: `m/a + (n-m)/a + [m%a > n%a] = n/a`. -/
theorem carry (a m n : ℕ) (ha : 0 < a) (hm : m ≤ n) :
    m / a + (n - m) / a + (if m % a ≤ n % a then 0 else 1) = n / a := by
  have h1 := Nat.div_add_mod m a
  have h2 := Nat.div_add_mod (n - m) a
  have h3 := Nat.mod_lt m ha
  have h4 := Nat.mod_lt (n - m) ha
  set q1 := m / a
  set r1 := m % a
  set q2 := (n - m) / a
  set r2 := (n - m) % a
  by_cases h : r1 + r2 < a
  · have hu : n / a = q1 + q2 ∧ n % a = r1 + r2 := (Nat.div_mod_unique ha).2
      ⟨by rw [mul_add]; omega, h⟩
    rw [hu.1, hu.2]; split_ifs <;> omega
  · have hu : n / a = q1 + q2 + 1 ∧ n % a = r1 + r2 - a := (Nat.div_mod_unique ha).2
      ⟨by rw [mul_add, mul_add]; omega, by omega⟩
    rw [hu.1, hu.2]; split_ifs <;> omega

variable {p : ℕ} [hp : Fact p.Prime]

/-- `a = (p+1)/2`. -/
abbrev aa (p : ℕ) : ℕ := (p + 1) / 2

noncomputable def dd (p n : ℕ) : ℚ := (p : ℚ) ^ (n / aa p) * cQ n

noncomputable def gg (p j : ℕ) : ℚ := (p : ℚ) ^ (j / aa p) * fQ j

theorem gg_pint (hp4 : p % 4 = 3) (j : ℕ) : Pint p (gg p j) := by
  have := Pint.of_val_le (p := p) (X := Pi3 j) (Y := (2 * j).factorial) (k := j / aa p)
    (Pi3_pos j).ne' (Nat.factorial_ne_zero _) (RomikWeight.weight_K hp4 j)
  unfold gg fQ
  rw [mul_div_assoc] at this
  exact this

theorem gg_red_zero (hp4 : p % 4 = 3) (j : ℕ) (hj : 2 * aa p ≤ j) :
    ((gg p j : ℚ) : ZMod p) = 0 := by
  have := Pint.cast_eq_zero_of_val_lt (p := p) (X := Pi3 j) (Y := (2 * j).factorial)
    (k := j / aa p) (Pi3_pos j).ne' (Nat.factorial_ne_zero _) (RomikWeight.weight_K_strict hp4 j hj)
  unfold gg fQ
  rw [mul_div_assoc] at this
  exact this

theorem aa_pos (p : ℕ) [hp : Fact p.Prime] : 0 < aa p := by
  have := hp.out.two_le; unfold aa; omega

/-- The normalised recurrence term. -/
theorem term_eq (n m : ℕ) (hm : m ≤ n) :
    (p : ℚ) ^ (n / aa p) * (cQ m * cQ (n - m)) =
      (if m % aa p ≤ n % aa p then 1 else (p : ℚ)) * (dd p m * dd p (n - m)) := by
  unfold dd
  have hc := carry (aa p) m n (aa_pos p) hm
  rw [← hc]
  split_ifs <;> ring

theorem dd_pint (hp4 : p % 4 = 3) (n : ℕ) : Pint p (dd p n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [dd, cQ_zero]; exact Pint.one
    have h2 : ¬ p ∣ 2 := by
      intro h
      have := Nat.le_of_dvd (by norm_num) h
      have := hp.out.two_le
      have : p = 2 := by omega
      omega
    have : dd p n = (gg p n - ∑ m ∈ Ico 1 n,
        (if m % aa p ≤ n % aa p then 1 else (p : ℚ)) * (dd p m * dd p (n - m))) / (2 : ℕ) := by
      rw [Finset.sum_congr rfl (fun m hm => (term_eq n m (by rw [Finset.mem_Ico] at hm; omega)).symm)]
      unfold dd gg
      rw [cQ_rec n hn, ← Finset.mul_sum]
      push_cast
      ring
    rw [this]
    refine Pint.div_nat (Pint.sub (gg_pint hp4 n) (Pint.sum _ _ (fun m hm => ?_))) h2
    rw [Finset.mem_Ico] at hm
    refine Pint.mul ?_ ((ih m (by omega)).mul (ih (n - m) (by omega)))
    split_ifs
    · exact Pint.one
    · exact Pint.natCast p

/-- The residues `D n = dd n mod p` and `Gr n = gg n mod p`. -/
noncomputable def D (p : ℕ) [Fact p.Prime] (n : ℕ) : ZMod p := ((dd p n : ℚ) : ZMod p)

noncomputable def Gr (p : ℕ) [Fact p.Prime] (n : ℕ) : ZMod p := ((gg p n : ℚ) : ZMod p)

theorem D_zero : D p 0 = 1 := by simp [D, dd, cQ_zero]

theorem Gr_zero : Gr p 0 = 1 := by simp [Gr, gg, fQ_zero]

/-- **No-carry recurrence** for the residues, `n ≥ 1`. -/
theorem noCarry_rec (hp4 : p % 4 = 3) (n : ℕ) (hn : 1 ≤ n) :
    ∑ m ∈ range (n + 1), (if m % aa p ≤ n % aa p then D p m * D p (n - m) else 0) = Gr p n := by
  -- rational identity
  have hq : 2 * dd p n + ∑ m ∈ Ico 1 n,
      (if m % aa p ≤ n % aa p then 1 else (p : ℚ)) * (dd p m * dd p (n - m)) = gg p n := by
    rw [Finset.sum_congr rfl (fun m hm => (term_eq n m (by rw [Finset.mem_Ico] at hm; omega)).symm)]
    unfold dd gg
    rw [← Finset.mul_sum, ← conv n hn]
    ring
  have hpd := dd_pint hp4
  have hterm : ∀ m ∈ Ico 1 n, Pint p ((if m % aa p ≤ n % aa p then 1 else (p : ℚ)) *
      (dd p m * dd p (n - m))) := by
    intro m _
    refine Pint.mul ?_ ((hpd m).mul (hpd (n - m)))
    split_ifs
    · exact Pint.one
    · exact Pint.natCast p
  have hc : (((2 * dd p n + ∑ m ∈ Ico 1 n,
      (if m % aa p ≤ n % aa p then 1 else (p : ℚ)) * (dd p m * dd p (n - m)) : ℚ)) : ZMod p) =
      ((gg p n : ℚ) : ZMod p) := by rw [hq]
  have h2p : Pint p (2 : ℚ) := by exact_mod_cast Pint.natCast (p := p) 2
  rw [Pint.cast_add (h2p.mul (hpd n)) (Pint.sum _ _ hterm),
    Pint.cast_mul h2p (hpd n), Pint.cast_sum _ _ hterm] at hc
  rw [Finset.sum_congr rfl (fun m _ => by
      rw [Pint.cast_mul (by split_ifs; exacts [Pint.one, Pint.natCast p]) ((hpd m).mul (hpd (n - m))),
        Pint.cast_mul (hpd m) (hpd (n - m))])] at hc
  -- split off `m = 0` and `m = n`
  rw [Finset.sum_range_succ, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < n)]
  have h0 : (0 : ℕ) % aa p ≤ n % aa p := by simp
  have hsum : ∑ m ∈ Ico (0 + 1) n, (if m % aa p ≤ n % aa p then D p m * D p (n - m) else 0) =
      ∑ m ∈ Ico 1 n, ((((if m % aa p ≤ n % aa p then 1 else (p : ℚ)) : ℚ) : ZMod p) *
        (((dd p m : ℚ) : ZMod p) * ((dd p (n - m) : ℚ) : ZMod p))) := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    unfold D
    split_ifs
    · simp
    · simp
  rw [hsum]
  unfold Gr
  rw [← hc]
  simp only [h0, le_refl, ↓reduceIte, Nat.sub_zero, Nat.sub_self, D_zero]
  unfold D
  push_cast
  ring

end Romik
```

### `RomikPoly.lean`

```lean
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The explicit square root in `F_p[x][y] / (x^a)` (the analytic-to-finite step)

Let `p` be an odd prime, `a = (p+1)/2`, `h = (p-1)/2`.  Given residues `Gq : ℕ → ZMod p` with
`Gq 0 = 1` and `Gq n = 0` for `n ≥ 2a`, put `F0 = Σ_{r<a} Gq r x^r`, `W1 = Σ_{r<a} Gq (a+r) x^r`,
`G = F0 + W1·y` and `c = Gq a`.  Then
`E_M = G^a · expand_p (Π_{i<M} (1 + c y^(p^i))^h)` satisfies `E_M^2 ≡ G (mod x^a, y^(p^(M+1)))`.
Consequently any sequence `Dd` with `Dd 0 = 1` that satisfies the no-carry recurrence
`Σ_{m≤n, m%a ≤ n%a} Dd m Dd (n-m) = Gq n` (`n ≥ 1`) is given by
`Dd n = [y^(n/a) x^(n%a)] E_M` whenever `n/a < p^(M+1)`.
-/

open Finset Polynomial

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace RomikPoly

variable {p : ℕ} [hp : Fact p.Prime]

/-- Coefficient of `y^K x^R`. -/
noncomputable def co (P : (ZMod p)[X][X]) (K R : ℕ) : ZMod p := (P.coeff K).coeff R

section defs

variable (Gq : ℕ → ZMod p)

noncomputable def F0 : (ZMod p)[X] := ∑ r ∈ range ((p + 1) / 2), C (Gq r) * X ^ r

noncomputable def W1 : (ZMod p)[X] := ∑ r ∈ range ((p + 1) / 2), C (Gq ((p + 1) / 2 + r)) * X ^ r

noncomputable def GG : (ZMod p)[X][X] := C (F0 Gq) + C (W1 Gq) * X

noncomputable def QQ (M : ℕ) : (ZMod p)[X][X] :=
  ∏ i ∈ range M, (1 + C (C (Gq ((p + 1) / 2))) * X ^ (p ^ i)) ^ ((p - 1) / 2)

noncomputable def EE (M : ℕ) : (ZMod p)[X][X] :=
  GG Gq ^ ((p + 1) / 2) * expand (ZMod p)[X] p (QQ Gq M)

end defs

theorem coeff_sum_mono {R : Type*} [Semiring R] (g : ℕ → R) (N r : ℕ) :
    (∑ i ∈ range N, C (g i) * X ^ i : R[X]).coeff r = if r < N then g r else 0 := by
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

variable (Gq : ℕ → ZMod p)

theorem F0_coeff (r : ℕ) : (F0 Gq).coeff r = if r < (p + 1) / 2 then Gq r else 0 :=
  coeff_sum_mono _ _ _

theorem W1_coeff (r : ℕ) :
    (W1 Gq).coeff r = if r < (p + 1) / 2 then Gq ((p + 1) / 2 + r) else 0 :=
  coeff_sum_mono (fun i => Gq ((p + 1) / 2 + i)) _ _

theorem GG_coeff (K : ℕ) :
    (GG Gq).coeff K = if K = 0 then F0 Gq else if K = 1 then W1 Gq else 0 := by
  unfold GG
  rw [coeff_add, coeff_C, coeff_C_mul_X]
  rcases K with _ | _ | K <;> simp

/-! ### The ideal `(x^a, y^N)` and its coefficients -/

theorem co_ideal_zero (N : ℕ) (z : (ZMod p)[X][X])
    (hz : z ∈ Ideal.span ({C (X ^ ((p + 1) / 2)), X ^ N} : Set (ZMod p)[X][X]))
    (K R : ℕ) (hR : R < (p + 1) / 2) (hK : K < N) : co z K R = 0 := by
  obtain ⟨u, v, rfl⟩ := Ideal.mem_span_pair.1 hz
  unfold co
  have h1 : ¬ ((p + 1) / 2 ≤ R) := by omega
  have h2 : ¬ (N ≤ K) := by omega
  rw [coeff_add, coeff_mul_C, coeff_mul_X_pow', coeff_add, coeff_mul_X_pow']
  simp [h1, h2]

/-! ### Frobenius facts -/

theorem frob_C (q : (ZMod p)[X]) : (C q : (ZMod p)[X][X]) ^ p = C (q ^ p) := by
  rw [map_pow]

theorem cc_pow (x : ZMod p) : (C (C x) : (ZMod p)[X][X]) ^ p = C (C x) := by
  rw [← map_pow, ← map_pow, ZMod.pow_card]

/-- Telescoping: `(1 + c y) Π_{i<M} (1 + c y^(p^i))^(p-1) = 1 + c y^(p^M)`. -/
theorem telescope (x : ZMod p) (hp2 : p ≠ 2) (M : ℕ) :
    (1 + C (C x) * X) * (∏ i ∈ range M, (1 + C (C x) * X ^ (p ^ i)) ^ ((p - 1) / 2)) ^ 2 =
      (1 + C (C x) * X ^ (p ^ M) : (ZMod p)[X][X]) := by
  have hpodd : 2 * ((p - 1) / 2) + 1 = p := by
    have := hp.out.two_le
    rcases hp.out.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  induction M with
  | zero => simp
  | succ M ih =>
    rw [prod_range_succ, mul_pow, ← mul_assoc, ih, ← pow_mul, ← pow_succ',
      mul_comm ((p - 1) / 2) 2, hpodd, add_pow_char, one_pow, mul_pow, cc_pow, ← pow_mul,
      pow_succ]

/-! ### The square identity -/

theorem X_dvd_sub_C (q : (ZMod p)[X]) : (X : (ZMod p)[X]) ∣ q - C (q.coeff 0) := by
  rw [X_dvd_iff, coeff_sub, coeff_C_zero, sub_self]

theorem pow_sub_mem (q : (ZMod p)[X]) :
    (X : (ZMod p)[X]) ^ ((p + 1) / 2) ∣ q ^ p - C (q.coeff 0) := by
  have h1 : q ^ p - C (q.coeff 0) = (q - C (q.coeff 0)) ^ p := by
    rw [sub_pow_char, ← map_pow, ZMod.pow_card]
  rw [h1]
  have hle : (p + 1) / 2 ≤ p := by omega
  exact (pow_dvd_pow X hle).trans (pow_dvd_pow_of_dvd (X_dvd_sub_C q) p)

theorem sq_mem (hp2 : p ≠ 2) (h0 : Gq 0 = 1) (M : ℕ) :
    EE Gq M ^ 2 - GG Gq ∈
      Ideal.span ({C (X ^ ((p + 1) / 2)), X ^ (p ^ (M + 1))} : Set (ZMod p)[X][X]) := by
  set I := Ideal.span ({C (X ^ ((p + 1) / 2)), X ^ (p ^ (M + 1))} : Set (ZMod p)[X][X])
  set π := Ideal.Quotient.mk I
  rw [← Ideal.Quotient.eq]
  set c : ZMod p := Gq ((p + 1) / 2)
  have hpodd : (p + 1) / 2 * 2 = p + 1 := by
    have := hp.out.two_le
    rcases hp.out.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hmemA : C (X ^ ((p + 1) / 2)) ∈ I := Ideal.subset_span (by simp)
  have hmemY : (X ^ (p ^ (M + 1)) : (ZMod p)[X][X]) ∈ I := Ideal.subset_span (by simp)
  -- `F0^p ≡ 1` and `W1^p ≡ c` modulo `x^a`
  have hF : π (C (F0 Gq ^ p)) = π 1 := by
    obtain ⟨H, hH⟩ := pow_sub_mem (F0 Gq)
    have hc0 : (F0 Gq).coeff 0 = 1 := by
      rw [F0_coeff]; simp only [show 0 < (p + 1) / 2 by omega, ↓reduceIte, h0]
    rw [hc0, map_one] at hH
    have : F0 Gq ^ p = 1 + X ^ ((p + 1) / 2) * H := by rw [← hH]; ring
    refine Ideal.Quotient.eq.2 ?_
    rw [this, map_add, map_one, map_mul, add_sub_cancel_left]
    exact Ideal.mul_mem_right _ _ hmemA
  have hW : π (C (W1 Gq ^ p)) = π (C (C c)) := by
    obtain ⟨H, hH⟩ := pow_sub_mem (W1 Gq)
    have hc0 : (W1 Gq).coeff 0 = c := by
      rw [W1_coeff]; simp only [show 0 < (p + 1) / 2 by omega, ↓reduceIte, add_zero]; rfl
    rw [hc0] at hH
    have : W1 Gq ^ p = C c + X ^ ((p + 1) / 2) * H := by rw [← hH]; ring
    refine Ideal.Quotient.eq.2 ?_
    rw [this, map_add, map_mul, add_sub_cancel_left]
    exact Ideal.mul_mem_right _ _ hmemA
  have hGp : π (GG Gq ^ p) = π (1 + C (C c) * X ^ p) := by
    unfold GG
    rw [add_pow_char, mul_pow, frob_C, frob_C, map_add, map_mul, hF, hW, ← map_mul, ← map_add]
  -- the square
  have hE : EE Gq M ^ 2 = GG Gq * (GG Gq ^ p *
      expand (ZMod p)[X] p ((QQ Gq M) ^ 2)) := by
    unfold EE
    rw [mul_pow, ← pow_mul, hpodd, map_pow, pow_succ]
    ring
  have htel : (1 + C (C c) * X) * (QQ Gq M) ^ 2 = 1 + C (C c) * X ^ (p ^ M) :=
    telescope c hp2 M
  have hexp : (1 + C (C c) * X ^ p) * expand (ZMod p)[X] p ((QQ Gq M) ^ 2) =
      1 + C (C c) * X ^ (p ^ (M + 1)) := by
    have := congrArg (expand (ZMod p)[X] p) htel
    simp only [map_mul, map_add, map_one, expand_C, map_pow, expand_X] at this
    rw [map_pow, this, ← pow_mul, ← pow_succ']
  have hlast : π (1 + C (C c) * X ^ (p ^ (M + 1))) = π 1 := by
    refine Ideal.Quotient.eq.2 ?_
    rw [add_sub_cancel_left]
    exact Ideal.mul_mem_left _ _ hmemY
  rw [hE, map_mul, map_mul, hGp, ← map_mul, hexp, hlast, ← map_mul, mul_one]

/-! ### Coefficients of a square -/

theorem co_mul (A B : (ZMod p)[X][X]) (K R : ℕ) :
    co (A * B) K R = ∑ K1 ∈ range (K + 1), ∑ R1 ∈ range (R + 1),
      co A K1 R1 * co B (K - K1) (R - R1) := by
  unfold co
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, finsetSum_coeff]
  refine Finset.sum_congr rfl (fun K1 _ => ?_)
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

theorem co_GG (K R : ℕ) (hR : R < (p + 1) / 2) (hG : ∀ n, 2 * ((p + 1) / 2) ≤ n → Gq n = 0) :
    co (GG Gq) K R = Gq ((p + 1) / 2 * K + R) := by
  unfold co
  rw [GG_coeff]
  rcases K with _ | _ | K
  · simp [F0_coeff, hR]
  · simp [W1_coeff, hR]
  · simp only [show K + 2 ≠ 0 by omega, show K + 2 ≠ 1 by omega, ↓reduceIte, coeff_zero]
    rw [hG]
    nlinarith

theorem co_EE_zero (M : ℕ) (h0 : Gq 0 = 1) : co (EE Gq M) 0 0 = 1 := by
  unfold co EE
  rw [coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero]
  simp only [eval_mul, eval_pow, expand_eval]
  have hG : eval 0 (GG Gq) = F0 Gq := by unfold GG; simp
  have hQ : eval (0 ^ p) (QQ Gq M) = 1 := by
    unfold QQ
    rw [zero_pow hp.out.ne_zero, eval_prod]
    refine Finset.prod_eq_one (fun i _ => ?_)
    simp [zero_pow (pow_ne_zero i hp.out.ne_zero)]
  rw [hG, hQ]
  simp only [eval_one, mul_one, eval_pow]
  rw [← coeff_zero_eq_eval_zero, F0_coeff]
  have : 0 < (p + 1) / 2 := by have := hp.out.two_le; omega
  simp only [this, ↓reduceIte, h0, one_pow]

/-! ### Re-indexing the no-carry convolution -/

theorem reindex (a n : ℕ) (ha : 0 < a) (g : ℕ → ZMod p) :
    ∑ m ∈ range (n + 1), (if m % a ≤ n % a then g m else 0) =
      ∑ K1 ∈ range (n / a + 1), ∑ R1 ∈ range (n % a + 1), g (a * K1 + R1) := by
  rw [← Finset.sum_filter, ← Finset.sum_product']
  rw [← Finset.sum_image (s := range (n / a + 1) ×ˢ range (n % a + 1))
    (g := fun x : ℕ × ℕ => a * x.1 + x.2) (f := g)]
  · congr 1
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_product,
      Prod.exists]
    constructor
    · rintro ⟨hm, hr⟩
      refine ⟨m / a, m % a, ⟨?_, by omega⟩, Nat.div_add_mod m a⟩
      have := Nat.div_le_div_right (c := a) (show m ≤ n by omega)
      omega
    · rintro ⟨K1, R1, ⟨hK1, hR1⟩, rfl⟩
      have hR1a : R1 < a := lt_of_le_of_lt (by omega) (Nat.mod_lt n ha)
      have hmod : (a * K1 + R1) % a = R1 := by
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hR1a]
      refine ⟨?_, by rw [hmod]; omega⟩
      have h1 := Nat.div_add_mod n a
      have h2 : a * K1 ≤ a * (n / a) := Nat.mul_le_mul_left a (by omega)
      omega
  · rintro ⟨K1, R1⟩ h1 ⟨K2, R2⟩ h2 heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at h1 h2
    simp only at heq
    have hR1a : R1 < a := lt_of_le_of_lt (by omega) (Nat.mod_lt n ha)
    have hR2a : R2 < a := lt_of_le_of_lt (by omega) (Nat.mod_lt n ha)
    have e1 : (a * K1 + R1) % a = R1 := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hR1a]
    have e2 : (a * K2 + R2) % a = R2 := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hR2a]
    have e3 : (a * K1 + R1) / a = K1 := by
      rw [Nat.mul_add_div ha, Nat.div_eq_of_lt hR1a, add_zero]
    have e4 : (a * K2 + R2) / a = K2 := by
      rw [Nat.mul_add_div ha, Nat.div_eq_of_lt hR2a, add_zero]
    rw [heq] at e1 e3
    rw [Prod.mk.injEq]
    exact ⟨by rw [← e3, e4], by rw [← e1, e2]⟩

/-! ### The main identification -/

theorem main (hp2 : p ≠ 2) (h0 : Gq 0 = 1) (hG : ∀ n, 2 * ((p + 1) / 2) ≤ n → Gq n = 0)
    (Dd : ℕ → ZMod p) (hD0 : Dd 0 = 1)
    (hrec : ∀ n, 1 ≤ n → ∑ m ∈ range (n + 1),
      (if m % ((p + 1) / 2) ≤ n % ((p + 1) / 2) then Dd m * Dd (n - m) else 0) = Gq n)
    (M n : ℕ) (hn : n / ((p + 1) / 2) < p ^ (M + 1)) :
    Dd n = co (EE Gq M) (n / ((p + 1) / 2)) (n % ((p + 1) / 2)) := by
  set a := (p + 1) / 2 with ha_def
  have ha : 0 < a := by have := hp.out.two_le; omega
  set E' : ℕ → ZMod p := fun m => co (EE Gq M) (m / a) (m % a) with hE'
  -- the square identity, read off at `(n/a, n%a)`
  have hsq : ∀ n, 1 ≤ n → n / a < p ^ (M + 1) → ∑ m ∈ range (n + 1),
      (if m % a ≤ n % a then E' m * E' (n - m) else 0) = Gq n := by
    intro n _ hn
    have hz := co_ideal_zero (p := p) (p ^ (M + 1)) _ (sq_mem Gq hp2 h0 M) (n / a) (n % a)
      (Nat.mod_lt n ha) hn
    unfold co at hz
    rw [coeff_sub, coeff_sub, sub_eq_zero] at hz
    have hz' : co (EE Gq M * EE Gq M) (n / a) (n % a) = co (GG Gq) (n / a) (n % a) := by
      unfold co; rw [← pow_two]; exact hz
    rw [co_mul, co_GG Gq _ _ (Nat.mod_lt n ha) hG, Nat.div_add_mod] at hz'
    rw [← hz', reindex a n ha (fun m => E' m * E' (n - m))]
    refine Finset.sum_congr rfl (fun K1 hK1 => Finset.sum_congr rfl (fun R1 hR1 => ?_))
    rw [Finset.mem_range] at hK1 hR1
    have hR1a : R1 < a := lt_of_le_of_lt (by omega) (Nat.mod_lt n ha)
    have h1 := Nat.div_add_mod n a
    have hle : a * K1 + R1 ≤ n := by
      have : a * K1 ≤ a * (n / a) := Nat.mul_le_mul_left a (by omega)
      omega
    have hsub : n - (a * K1 + R1) = a * (n / a - K1) + (n % a - R1) := by
      rw [Nat.mul_sub]; have : a * K1 ≤ a * (n / a) := Nat.mul_le_mul_left a (by omega)
      omega
    have hR2 : n % a - R1 < a := by have := Nat.mod_lt n ha; omega
    simp only [hE']
    rw [hsub, Nat.mul_add_div ha, Nat.div_eq_of_lt hR1a, Nat.mul_add_div ha,
      Nat.div_eq_of_lt hR2, Nat.mul_add_mod, Nat.mod_eq_of_lt hR1a, Nat.mul_add_mod,
      Nat.mod_eq_of_lt hR2, add_zero, add_zero]
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    have := hp.out.two_le
    omega
  -- strong induction
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn1
    · simp only [hD0, Nat.zero_div, Nat.zero_mod]
      exact (co_EE_zero Gq M h0).symm
    have hA := hrec n hn1
    have hB := hsq n hn1 hn
    have split : ∀ f : ℕ → ZMod p, f 0 = f n → (f 0 = Dd n ∨ True) →
        ∑ m ∈ range (n + 1), f m = 2 * f 0 + ∑ m ∈ Ico 1 n, f m := by
      intro f hf _
      rw [Finset.sum_range_succ, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hn1, ← hf]
      ring
    have h00 : (0 : ℕ) % a ≤ n % a := by simp
    rw [split _ (by simp [Nat.sub_self, Nat.sub_zero, mul_comm]) (Or.inr trivial)] at hA hB
    simp only [h00, ↓reduceIte, Nat.sub_zero, hD0, one_mul] at hA hB
    have hE0 : E' 0 = 1 := by simp only [hE', Nat.zero_div, Nat.zero_mod]; exact co_EE_zero Gq M h0
    rw [hE0, one_mul] at hB
    have hsum : ∑ m ∈ Ico 1 n, (if m % a ≤ n % a then Dd m * Dd (n - m) else 0) =
        ∑ m ∈ Ico 1 n, (if m % a ≤ n % a then E' m * E' (n - m) else 0) := by
      refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [Finset.mem_Ico] at hm
      have hma : m / a < p ^ (M + 1) :=
        lt_of_le_of_lt (Nat.div_le_div_right (by omega)) hn
      have hnma : (n - m) / a < p ^ (M + 1) :=
        lt_of_le_of_lt (Nat.div_le_div_right (by omega)) hn
      rw [ih m (by omega) hma, ih (n - m) (by omega) hnma]
    rw [hsum] at hA
    have : 2 * Dd n = 2 * E' n := by linear_combination hA - hB
    exact mul_left_cancel₀ h2 this

end RomikPoly
```

### `RomikDigits.lean`

```lean
import RomikPoly

/-!
# Reading the coefficients of `E_M` digit by digit

`[y^K](A · expand_p B) = A_{K mod p} · B_{K / p}` when `deg A < p`.  Hence
* `[y^K] E_M = 0` whenever `K mod p > a`;
* for `M = 2` (valid for `K < p^3`) the coefficient is an explicit product over the three
  base-`p` digits `k0, k1, k2` of `K`.
-/

open Finset Polynomial

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace RomikPoly

variable {p : ℕ} [hp : Fact p.Prime]

theorem coeff_mul_expand {R : Type*} [CommSemiring R] (A B : R[X]) (hA : A.natDegree < p)
    (K : ℕ) : (A * expand R p B).coeff K = A.coeff (K % p) * B.coeff (K / p) := by
  have hp0 : 0 < p := hp.out.pos
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_eq_single (K % p)]
  · simp only
    rw [coeff_expand hp0]
    have hdvd : p ∣ K - K % p := Nat.dvd_sub_mod K
    simp only [hdvd, ↓reduceIte]
    congr 2
    have h1 := Nat.div_add_mod K p
    have : K - K % p = p * (K / p) := by omega
    rw [this, Nat.mul_div_cancel_left _ hp0]
  · intro j hj hne
    rw [Finset.mem_range] at hj
    by_cases hjA : A.natDegree < j
    · rw [coeff_eq_zero_of_natDegree_lt hjA, zero_mul]
    · rw [coeff_expand hp0]
      have hjp : j < p := by omega
      have : ¬ p ∣ K - j := by
        rintro ⟨t, ht⟩
        apply hne
        have : K = p * t + j := by omega
        rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt hjp]
      simp [this]
  · intro h
    exfalso; apply h
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.mod_le K p)

variable (Gq : ℕ → ZMod p)

theorem natDegree_GG_pow (hp2 : p ≠ 2) : ((GG Gq) ^ ((p + 1) / 2)).natDegree < p := by
  have h1 : (GG Gq).natDegree ≤ 1 := by
    unfold GG
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · rw [natDegree_C]; exact Nat.zero_le _
    · exact (natDegree_C_mul_le _ _).trans natDegree_X_le
  have h2 := natDegree_pow_le (p := GG Gq) (n := (p + 1) / 2)
  have h3 : 3 ≤ p := by
    have := hp.out.two_le
    omega
  calc _ ≤ (p + 1) / 2 * (GG Gq).natDegree := h2
    _ ≤ (p + 1) / 2 * 1 := Nat.mul_le_mul_left _ h1
    _ < p := by omega

theorem natDegree_lin_pow (x : ZMod p) (hp2 : p ≠ 2) :
    ((1 + C (C x) * X : (ZMod p)[X][X]) ^ ((p - 1) / 2)).natDegree < p := by
  have h1 : (1 + C (C x) * X : (ZMod p)[X][X]).natDegree ≤ 1 := by
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · rw [natDegree_one]; exact Nat.zero_le _
    · exact (natDegree_C_mul_le _ _).trans natDegree_X_le
  have h2 := natDegree_pow_le (p := (1 + C (C x) * X : (ZMod p)[X][X])) (n := (p - 1) / 2)
  have h3 : 3 ≤ p := by
    have := hp.out.two_le
    omega
  calc _ ≤ (p - 1) / 2 * (1 + C (C x) * X : (ZMod p)[X][X]).natDegree := h2
    _ ≤ (p - 1) / 2 * 1 := Nat.mul_le_mul_left _ h1
    _ < p := by omega

theorem GG_pow_coeff (j : ℕ) :
    ((GG Gq) ^ ((p + 1) / 2)).coeff j =
      ((Nat.choose ((p + 1) / 2) j : ℕ) : (ZMod p)[X]) *
        (W1 Gq ^ j * F0 Gq ^ ((p + 1) / 2 - j)) := by
  have hG : GG Gq = C (W1 Gq) * X + C (F0 Gq) := by unfold GG; ring
  rw [hG, add_pow, finsetSum_coeff]
  have hterm : ∀ m, (C (W1 Gq) * X) ^ m * C (F0 Gq) ^ ((p + 1) / 2 - m) *
      ((Nat.choose ((p + 1) / 2) m : ℕ) : (ZMod p)[X][X]) =
      C (((Nat.choose ((p + 1) / 2) m : ℕ) : (ZMod p)[X]) *
        (W1 Gq ^ m * F0 Gq ^ ((p + 1) / 2 - m))) * X ^ m := by
    intro m
    simp only [map_mul, map_pow, map_natCast, mul_pow]
    ring
  simp_rw [hterm, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Finset.mem_range] at h
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

theorem lin_pow_coeff (x : ZMod p) (h j : ℕ) :
    ((1 + C (C x) * X : (ZMod p)[X][X]) ^ h).coeff j =
      C (x ^ j * (Nat.choose h j : ZMod p)) := by
  rw [add_comm, add_pow, finsetSum_coeff]
  have hterm : ∀ m, (C (C x) * X : (ZMod p)[X][X]) ^ m * 1 ^ (h - m) *
      ((Nat.choose h m : ℕ) : (ZMod p)[X][X]) = C (C (x ^ m * (Nat.choose h m : ZMod p))) * X ^ m := by
    intro m
    simp only [map_mul, map_pow, map_natCast, mul_pow, one_pow, mul_one]
    ring
  simp_rw [hterm, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h'
  · rfl
  · rw [Finset.mem_range] at h'
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- The odd-clause vanishing: `[y^K] E_M = 0` whenever `K mod p > a`. -/
theorem co_EE_eq_zero (hp2 : p ≠ 2) (M K R : ℕ) (hK : (p + 1) / 2 < K % p) :
    co (EE Gq M) K R = 0 := by
  unfold co EE
  rw [coeff_mul_expand _ _ (natDegree_GG_pow Gq hp2), GG_pow_coeff,
    Nat.choose_eq_zero_of_lt hK]
  simp

theorem QQ_two : QQ Gq 2 = (1 + C (C (Gq ((p + 1) / 2))) * X) ^ ((p - 1) / 2) *
    expand (ZMod p)[X] p ((1 + C (C (Gq ((p + 1) / 2))) * X) ^ ((p - 1) / 2)) := by
  unfold QQ
  simp [Finset.prod_range_succ, map_pow, expand_X]

/-- The three-digit formula for `M = 2`. -/
theorem co_EE_two (hp2 : p ≠ 2) (K R : ℕ) :
    co (EE Gq 2) K R =
      (Nat.choose ((p + 1) / 2) (K % p) : ZMod p) *
        (Gq ((p + 1) / 2) ^ (K / p % p) * (Nat.choose ((p - 1) / 2) (K / p % p) : ZMod p)) *
        (Gq ((p + 1) / 2) ^ (K / p / p) * (Nat.choose ((p - 1) / 2) (K / p / p) : ZMod p)) *
        (W1 Gq ^ (K % p) * F0 Gq ^ ((p + 1) / 2 - K % p)).coeff R := by
  unfold co EE
  rw [QQ_two, coeff_mul_expand _ _ (natDegree_GG_pow Gq hp2),
    coeff_mul_expand _ _ (natDegree_lin_pow _ hp2), GG_pow_coeff, lin_pow_coeff, lin_pow_coeff]
  rw [show ((Nat.choose ((p + 1) / 2) (K % p) : ℕ) : (ZMod p)[X]) =
      C ((Nat.choose ((p + 1) / 2) (K % p) : ℕ) : ZMod p) from (map_natCast C _).symm]
  rw [mul_assoc, ← map_mul, mul_comm, ← mul_assoc, coeff_mul_C, coeff_mul_C]
  ring

end RomikPoly
```

### `RomikArith.lean`

```lean
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Zify
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Ring.Parity

/-!
# The arithmetic of the thresholds

All statements are about natural numbers.  Notation: `a = (p+1)/2`, `K = n / a`, `R = n % a`,
`ν = ν_p((2n)!)`.  The `p`-adic valuation of `v(n) = 2^n (2n)! c_n` is `ν + ord_p(c_n)`, and
`ord_p(c_n) ≥ -K`, with equality iff the residue `D n` is nonzero (other modules).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace RomikArith

variable {p : ℕ} [hp : Fact p.Prime]

/-- Legendre, one step: `ν(m!) = ⌊m/p⌋ + ν(⌊m/p⌋!)`. -/
theorem vfact (m : ℕ) :
    padicValNat p m.factorial = m / p + padicValNat p (m / p).factorial := by
  have h1 := padicValNat_factorial_mul_add (p := p) (m / p) (Nat.mod_lt m hp.out.pos)
  rw [Nat.div_add_mod] at h1
  rw [h1, padicValNat_factorial_mul, add_comm]

theorem vfact_small (q : ℕ) (hq : q < p) : padicValNat p q.factorial = 0 := by
  rw [vfact, Nat.div_eq_of_lt hq]; simp

theorem vfact_ge (m : ℕ) : m / p ≤ padicValNat p m.factorial := by
  rw [vfact]; omega

/-- `φ`-bound: `K + T ≤ pT + S + τ + 1` (the written proof's estimate behind `ord ≥ e-1`). -/
theorem phi_bound {K R T S U τ : ℕ} (hm : (p + 1) * K + 2 * R = p * p * T + p * S + U)
    (hU : U + 1 ≤ p) (hT : T < p * (τ + 1)) : K + T ≤ p * T + S + τ + 1 := by
  by_contra h
  have h' : p * T + S + τ + 2 ≤ K + T := by omega
  have := Nat.mul_le_mul_left (p + 1) h'
  nlinarith

/-- Strict `φ`-bound when `T ≥ p²`. -/
theorem phi_bound_big {K R T S U τ1 τ2 : ℕ} (hm : (p + 1) * K + 2 * R = p * p * T + p * S + U)
    (hU : U + 1 ≤ p) (hT : T < p * (τ1 + 1)) (h12 : p * τ2 ≤ τ1) (h2 : 1 ≤ τ2) :
    K + T + 1 ≤ p * T + S + τ1 + τ2 := by
  by_contra h
  have h' : p * T + S + τ1 + τ2 ≤ K + T := by omega
  have := Nat.mul_le_mul_left (p + 1) h'
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  nlinarith

/-- **Odd clause arithmetic.** -/
theorem odd_arith (hp4 : p % 4 = 3) {e n : ℕ} (he : Odd e) (hn : (e * p + 2) * (p + 1) ≤ 4 * n) :
    n / ((p + 1) / 2) + e ≤ padicValNat p (2 * n).factorial ∨
      (n / ((p + 1) / 2) + e ≤ padicValNat p (2 * n).factorial + 1 ∧
        (p + 1) / 2 < n / ((p + 1) / 2) % p) := by
  obtain ⟨t, rfl⟩ := he
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  set a := (p + 1) / 2 with ha_def
  have ha : 2 * a = p + 1 := by omega
  have ha0 : 0 < a := by omega
  set K := n / a
  set R := n % a
  have hnK : a * K + R = n := Nat.div_add_mod n a
  have hR : R < a := Nat.mod_lt n ha0
  have hm : 2 * n = p * K + (K + 2 * R) := by nlinarith
  -- `K ≥ tp + a`
  have hKge : t * p + a ≤ K := by
    by_contra h
    have h1 : 2 * K ≤ 2 * (t * p) + p := by omega
    have := Nat.mul_le_mul_left (p + 1) h1
    nlinarith
  have hν : 2 * n / p + 2 * n / p / p ≤ padicValNat p (2 * n).factorial := by
    have := vfact_ge (p := p) (2 * n / p)
    have := vfact (p := p) (2 * n)
    omega
  have h1 : 2 * n / p = K + (K + 2 * R) / p := by
    rw [hm, add_comm, Nat.add_mul_div_left _ _ hp.out.pos, add_comm]
  have h2 : t ≤ 2 * n / p / p := by
    rw [Nat.le_div_iff_mul_le hp.out.pos, Nat.le_div_iff_mul_le hp.out.pos]
    nlinarith
  have h3 : t ≤ (K + 2 * R) / p := by
    rw [Nat.le_div_iff_mul_le hp.out.pos]; nlinarith
  by_cases hc : K + (2 * t + 1) ≤ padicValNat p (2 * n).factorial
  · exact Or.inl hc
  right
  have h4 : (K + 2 * R) / p = t := by omega
  have hlt : K + 2 * R < p * (t + 1) := by
    have := Nat.lt_mul_div_succ (K + 2 * R) hp.out.pos
    rw [h4] at this; exact this
  have hKne : K ≠ t * p + a := by
    intro hK
    have : a ≤ 2 * R := by
      rw [hK] at hnK
      nlinarith
    nlinarith
  refine ⟨by omega, ?_⟩
  have hu : K / p = t ∧ K % p = K - t * p := (Nat.div_mod_unique hp.out.pos).2
    ⟨by rw [mul_comm p t]; omega,
     by have : K < t * p + p := by nlinarith
        omega⟩
  rw [hu.2]
  omega

/-- Common setup for the even clause: the three base-`p` blocks of `m = 2n`. -/
theorem even_setup (n : ℕ) :
    ∃ T S U, 2 * n = p * p * T + p * S + U ∧ S < p ∧ U < p ∧
      padicValNat p (2 * n).factorial = p * T + S + T + padicValNat p T.factorial ∧
      2 * n / p / p = T := by
  refine ⟨2 * n / p / p, 2 * n / p % p, 2 * n % p, ?_, Nat.mod_lt _ hp.out.pos,
    Nat.mod_lt _ hp.out.pos, ?_, rfl⟩
  · have h1 := Nat.div_add_mod (2 * n) p
    have h2 := Nat.div_add_mod (2 * n / p) p
    nlinarith
  · rw [vfact (p := p) (2 * n), vfact (p := p) (2 * n / p)]
    have h2 := Nat.div_add_mod (2 * n / p) p
    omega

/-- **Even clause lower bound**: `K + e ≤ ν + 1`. -/
theorem even_lower (hp4 : p % 4 = 3) {e n : ℕ} (he : Even e) (hn : e * p ^ 2 ≤ 4 * n) :
    n / ((p + 1) / 2) + e ≤ padicValNat p (2 * n).factorial + 1 := by
  obtain ⟨t, rfl⟩ := he
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  set a := (p + 1) / 2 with ha_def
  have ha : 2 * a = p + 1 := by omega
  have ha0 : 0 < a := by omega
  set K := n / a
  set R := n % a
  have hnK : a * K + R = n := Nat.div_add_mod n a
  have hR : R < a := Nat.mod_lt n ha0
  obtain ⟨T, S, U, hm, hS, hU, hν, hT⟩ := even_setup (p := p) n
  rw [hν]
  have hm' : (p + 1) * K + 2 * R = p * p * T + p * S + U := by nlinarith
  have htT : t ≤ T := by
    rw [← hT, Nat.le_div_iff_mul_le hp.out.pos, Nat.le_div_iff_mul_le hp.out.pos]
    nlinarith
  have hτ := vfact_ge (p := p) T
  have hphi := phi_bound (p := p) hm' (by omega) (Nat.lt_mul_div_succ T hp.out.pos)
  omega

set_option maxHeartbeats 800000 in
/-- **Even clause confinement and digit collapse.** If `ν < K + e` then `K < p^3`, and if
moreover the digits of `K` are at most `(a, h, h)` (the nonvanishing condition of the residue),
then `e = (p+1)(2j+1)` with `j = K/p/p`, `2j < p-1`, `K % p = a`, `K/p % p = h`, and
`4n = ep^2 + (p+1) + 4r` with `r = n % a`, `4r < p+1`. -/
theorem even_conf (hp4 : p % 4 = 3) {e n : ℕ} (he : Even e) (hn : e * p ^ 2 ≤ 4 * n)
    (hlt : padicValNat p (2 * n).factorial < n / ((p + 1) / 2) + e) :
    n / ((p + 1) / 2) < p ^ 3 ∧
    (n / ((p + 1) / 2) % p ≤ (p + 1) / 2 → n / ((p + 1) / 2) / p % p ≤ (p - 1) / 2 →
      n / ((p + 1) / 2) / p / p ≤ (p - 1) / 2 →
      n / ((p + 1) / 2) % p = (p + 1) / 2 ∧ n / ((p + 1) / 2) / p % p = (p - 1) / 2 ∧
      2 * (n / ((p + 1) / 2) / p / p) < p - 1 ∧
      e = (p + 1) * (2 * (n / ((p + 1) / 2) / p / p) + 1) ∧
      4 * (n % ((p + 1) / 2)) < p + 1 ∧
      4 * n = e * p ^ 2 + (p + 1) + 4 * (n % ((p + 1) / 2))) := by
  obtain ⟨t, rfl⟩ := he
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  set a := (p + 1) / 2 with ha_def
  have ha : 2 * a = p + 1 := by omega
  have ha0 : 0 < a := by omega
  set K := n / a
  set R := n % a
  have hnK : a * K + R = n := Nat.div_add_mod n a
  have hR : R < a := Nat.mod_lt n ha0
  obtain ⟨T, S, U, hm, hS, hU, hν, hT⟩ := even_setup (p := p) n
  rw [hν] at hlt
  have hm' : (p + 1) * K + 2 * R = p * p * T + p * S + U := by nlinarith
  have htT : t ≤ T := by
    rw [← hT, Nat.le_div_iff_mul_le hp.out.pos, Nat.le_div_iff_mul_le hp.out.pos]
    nlinarith
  have hτ := vfact_ge (p := p) T
  have hphi := phi_bound (p := p) hm' (by omega) (Nat.lt_mul_div_succ T hp.out.pos)
  have hTt : T = t := by omega
  have hexact : K + T = p * T + S + padicValNat p T.factorial + 1 := by omega
  -- `T < p^2`
  have hTp : T < p * p := by
    by_contra hbig
    rw [not_lt] at hbig
    have hτ1 := vfact (p := p) T
    have hτ2 := vfact_ge (p := p) (T / p)
    have h12 : p * (T / p / p) ≤ T / p := Nat.mul_div_le (T / p) p
    have h2 : 1 ≤ T / p / p := by
      rw [Nat.le_div_iff_mul_le hp.out.pos, Nat.le_div_iff_mul_le hp.out.pos]; linarith
    have := phi_bound_big (p := p) hm' (by omega) (Nat.lt_mul_div_succ T hp.out.pos) h12 h2
    omega
  -- digits of `t`
  obtain ⟨q, r0, htq, hr0, hqdef⟩ : ∃ q r0, p * q + r0 = t ∧ r0 < p ∧ q = t / p :=
    ⟨t / p, t % p, Nat.div_add_mod t p, Nat.mod_lt t hp.out.pos, rfl⟩
  have hq : q < p := by
    rw [hqdef, Nat.div_lt_iff_lt_mul hp.out.pos]; rw [← hTt]; linarith
  have hνt : padicValNat p t.factorial = q := by
    rw [vfact (p := p) t, ← hqdef, vfact_small q hq, add_zero]
  rw [hTt, hνt] at hexact
  rw [hTt] at hm'
  -- relation (*): `U + r0 = 2R + S + q + p + 1`
  have hstar : U + r0 = 2 * R + S + q + p + 1 := by
    have e1 : (p + 1) * (K + t) = (p + 1) * (p * t + S + q + 1) := by rw [hexact]
    zify at e1 hm' htq ⊢
    linear_combination e1 - hm' + htq
  -- digits of `K`
  obtain ⟨k0, hk0⟩ : ∃ k0, k0 + 2 * R = U := ⟨U - 2 * R, by omega⟩
  obtain ⟨k1, hk1⟩ : ∃ k1, k1 + q + 1 = r0 := ⟨r0 - q - 1, by omega⟩
  have hKd : K = p * p * q + p * k1 + k0 := by
    have e1 : K + t = p * t + S + q + 1 := hexact
    zify at e1 htq hk0 hk1 hstar ⊢
    linear_combination e1 - ((p : ℤ) - 1) * htq - hstar - hk0 - (p : ℤ) * hk1
  have hk0p : k0 < p := by omega
  have hk1p : k1 < p := by omega
  have hd1 : K / p = p * q + k1 ∧ K % p = k0 :=
    (Nat.div_mod_unique hp.out.pos).2 ⟨by rw [hKd]; ring, hk0p⟩
  have hd2 : (p * q + k1) / p = q ∧ (p * q + k1) % p = k1 :=
    (Nat.div_mod_unique hp.out.pos).2 ⟨by ring, hk1p⟩
  refine ⟨?_, ?_⟩
  · rw [hKd]
    have h2 := Nat.mul_le_mul_left p (Nat.succ_le_of_lt hk1p)
    rw [Nat.mul_succ] at h2
    have h3 := Nat.mul_le_mul_left (p * p) (Nat.succ_le_of_lt hq)
    rw [Nat.mul_succ] at h3
    have h4 : p ^ 3 = p * p * p := by ring
    omega
  intro c0 c1 c2
  simp only [hd1.1, hd2.1, hd2.2, hd1.2] at c0 c1 c2 ⊢
  have hS0 : S = 0 := by omega
  have hk0a : k0 = a := by omega
  have hr0q : r0 = q + a := by omega
  have hk1h : k1 = (p - 1) / 2 := by omega
  refine ⟨hk0a, hk1h, by omega, ?_, by omega, ?_⟩
  · -- `e = 2t = (p+1)(2q+1)`
    have ht : t = p * q + q + a := by omega
    zify at ht ha ⊢
    linear_combination 2 * ht + ha
  · -- `4n = e p^2 + (p+1) + 4R`
    have hU' : U = a + 2 * R := by omega
    have h4 : 4 * n = 2 * (2 * n) := by ring
    rw [h4, hm, hTt, hS0, hU']
    zify at ha ⊢
    linear_combination ha

/-- **Even clause, converse arithmetic.** -/
theorem even_conv (hp4 : p % 4 = 3) {e n j r : ℕ} (hj : 2 * j < p - 1)
    (hej : e = (p + 1) * (2 * j + 1)) (hr : 4 * r < p + 1)
    (hn : 4 * n = e * p ^ 2 + (p + 1) + 4 * r) :
    n / ((p + 1) / 2) = p * p * j + p * ((p - 1) / 2) + (p + 1) / 2 ∧
    n % ((p + 1) / 2) = r ∧
    padicValNat p (2 * n).factorial + 1 = n / ((p + 1) / 2) + e := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  set a := (p + 1) / 2 with ha_def
  set h := (p - 1) / 2 with hh_def
  have ha : 2 * a = p + 1 := by omega
  have hh : 2 * h + 1 = p := by omega
  have ha0 : 0 < a := by omega
  have hah : a = h + 1 := by omega
  have hra : r < a := by omega
  set K0 := p * p * j + p * h + a
  have hnK : r + a * K0 = n := by
    have : 4 * (r + a * K0) = 4 * n := by
      rw [hn, hej]
      have : 4 * (a * K0) = 2 * (2 * a) * K0 := by ring
      rw [show 4 * (r + a * K0) = 4 * r + 4 * (a * K0) by ring, this, ha]
      simp only [K0]
      rw [show p = 2 * h + 1 from hh.symm, hah]
      ring
    omega
  have hu : n / a = K0 ∧ n % a = r := (Nat.div_mod_unique ha0).2 ⟨hnK, hra⟩
  refine ⟨hu.1, hu.2, ?_⟩
  rw [hu.1]
  -- `2n = t p^2 + U` with `t = (p+1)j + a`, `U = a + 2r < p`
  set t := p * j + (j + a)
  have hjap : j + a < p := by omega
  have hU : a + 2 * r < p := by omega
  have h2n : 2 * n = p * (p * t) + (a + 2 * r) := by
    have : 4 * n = 2 * (p * (p * t) + (a + 2 * r)) := by
      rw [hn, hej]
      simp only [t]
      rw [show p = 2 * h + 1 from hh.symm, hah]
      ring
    omega
  have hdiv1 : 2 * n / p = p * t := by
    rw [h2n, Nat.mul_add_div hp.out.pos, Nat.div_eq_of_lt hU, add_zero]
  have htj : t / p = j := by
    simp only [t]; rw [Nat.mul_add_div hp.out.pos, Nat.div_eq_of_lt hjap, add_zero]
  have hjp : j < p := by omega
  rw [vfact (p := p) (2 * n), hdiv1, padicValNat_factorial_mul, vfact (p := p) t, htj,
    vfact_small j hjp, hej]
  simp only [K0, t]
  rw [hah, ← hh]
  ring

end RomikArith
```

### `RomikLink.lean`

```lean
import RomikNorm
import RomikDigits

/-!
# Links: valuations of `v(n)`, the constant `c`, and `W1 ≡ c · smallW (mod x^d)`
-/

open Finset Polynomial

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Romik

variable {p : ℕ} [hp : Fact p.Prime]

theorem two_not_dvd (hp4 : p % 4 = 3) : ¬ p ∣ 2 := by
  intro h
  have := Nat.le_of_dvd (by norm_num) h
  have := hp.out.two_le
  omega

/-- `v(n) = 2^n · (2n)! · cQ n`, and `(2n)! = p^ν · u` with `p ∤ u`. -/
theorem romikV_decomp (n : ℕ) : ∃ u : ℕ, ¬ p ∣ u ∧
    (romikV n : ℚ) = 2 ^ n * (p : ℚ) ^ padicValNat p (2 * n).factorial * u * cQ n := by
  obtain ⟨u, hu, hfac⟩ := Pint.nat_decomp (p := p) (Nat.factorial_ne_zero (2 * n))
  refine ⟨u, hu, ?_⟩
  rw [← romikV_spec, romikQ_eq n]
  conv_lhs => rw [hfac]
  push_cast
  ring

theorem link_ge (hp4 : p % 4 = 3) (n e : ℕ)
    (h : n / aa p + e ≤ padicValNat p (2 * n).factorial) : (p : ℤ) ^ e ∣ romikV n := by
  obtain ⟨u, hu, hv⟩ := romikV_decomp (p := p) n
  apply Pint.int_dvd
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set ν := padicValNat p (2 * n).factorial
  have : (romikV n : ℚ) / (p : ℚ) ^ e =
      ((2 : ℕ) : ℚ) ^ n * (u : ℚ) * (p : ℚ) ^ (ν - (n / aa p) - e) * dd p n := by
    rw [hv]
    unfold dd
    have hν : (p : ℚ) ^ ν = (p : ℚ) ^ (ν - n / aa p - e) * (p : ℚ) ^ (n / aa p) * (p : ℚ) ^ e := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [hν]
    field_simp
    push_cast
    ring
  rw [this]
  exact (((Pint.natCast 2).pow n).mul (Pint.natCast u)).mul ((Pint.natCast p).pow _) |>.mul
    (dd_pint hp4 n)

theorem link_red (hp4 : p % 4 = 3) (n e : ℕ)
    (h : n / aa p + e ≤ padicValNat p (2 * n).factorial + 1) (hD : D p n = 0) :
    (p : ℤ) ^ e ∣ romikV n := by
  by_cases h' : n / aa p + e ≤ padicValNat p (2 * n).factorial
  · exact link_ge hp4 n e h'
  have heq : padicValNat p (2 * n).factorial + 1 = n / aa p + e := by omega
  obtain ⟨u, hu, hv⟩ := romikV_decomp (p := p) n
  apply Pint.int_dvd
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set ν := padicValNat p (2 * n).factorial
  have : (romikV n : ℚ) / (p : ℚ) ^ e = ((2 : ℕ) : ℚ) ^ n * (u : ℚ) * (dd p n / p) := by
    rw [hv]
    unfold dd
    have hν : (p : ℚ) ^ ν * p = (p : ℚ) ^ (n / aa p) * (p : ℚ) ^ e := by
      rw [← pow_succ, ← pow_add]; congr 1
    field_simp
    push_cast
    linear_combination (2 ^ n * u * cQ n : ℚ) * hν
  rw [this]
  exact (((Pint.natCast 2).pow n).mul (Pint.natCast u)).mul
    (Pint.div_p_of_cast_eq_zero (dd_pint hp4 n) hD)

theorem link_not (hp4 : p % 4 = 3) (n e : ℕ) (he : 1 ≤ e)
    (h : padicValNat p (2 * n).factorial + 1 = n / aa p + e) (hD : D p n ≠ 0) :
    ¬ (p : ℤ) ^ e ∣ romikV n := by
  rintro ⟨w, hw⟩
  obtain ⟨u, hu, hv⟩ := romikV_decomp (p := p) n
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set ν := padicValNat p (2 * n).factorial
  have h1 : (romikV n : ℚ) / (p : ℚ) ^ (e - 1) = ((2 : ℕ) : ℚ) ^ n * (u : ℚ) * dd p n := by
    rw [hv]
    unfold dd
    have hν : (p : ℚ) ^ ν = (p : ℚ) ^ (n / aa p) * (p : ℚ) ^ (e - 1) := by
      rw [← pow_add]; congr 1; omega
    rw [hν]
    field_simp
    push_cast
    ring
  have h2 : (romikV n : ℚ) / (p : ℚ) ^ (e - 1) = (p : ℚ) * w := by
    rw [hw]
    have : (p : ℚ) ^ e = (p : ℚ) * (p : ℚ) ^ (e - 1) := by
      rw [← pow_succ']; congr 1; omega
    push_cast
    rw [this]
    field_simp
  have h3 : ((((2 : ℕ) : ℚ) ^ n * (u : ℚ) * dd p n : ℚ) : ZMod p) = (((p : ℚ) * w : ℚ) : ZMod p) := by
    rw [← h1, ← h2]
  have hpu : Pint p (((2 : ℕ) : ℚ) ^ n * (u : ℚ)) := ((Pint.natCast 2).pow n).mul (Pint.natCast u)
  rw [Pint.cast_mul hpu (dd_pint hp4 n), Pint.cast_mul ((Pint.natCast 2).pow n) (Pint.natCast u),
    Pint.cast_mul (Pint.natCast p) (Pint.intCast w), Pint.cast_pow (Pint.natCast 2)] at h3
  simp only [Rat.cast_natCast, Rat.cast_intCast, ZMod.natCast_self, zero_mul] at h3
  have h2ne : ((2 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact two_not_dvd hp4
  have hune : ((u : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hu
  exact (mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2ne) hune) hD) h3

/-! ### The constant `c = Gr a ≠ 0` -/

theorem A4_not_dvd (hp4 : p % 4 = 3) : ¬ p ∣ A4 (aa p) := by
  unfold A4
  rw [Prime.dvd_finsetProd_iff hp.out.prime]
  rintro ⟨i, hi, hdvd⟩
  rw [Finset.mem_range] at hi
  obtain ⟨k, hk⟩ := hdvd
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have hk1 : k < 2 := by
    by_contra hk2
    have : p * 2 ≤ p * k := Nat.mul_le_mul_left p (by omega)
    unfold aa at hi
    omega
  interval_cases k <;> omega

theorem Gr_a_ne (hp4 : p % 4 = 3) : Gr p (aa p) ≠ 0 := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have ha : 2 * aa p = p + 1 := by unfold aa; omega
  have hpos : (p - 1).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hfact : (2 * aa p).factorial = (p + 1) * p * (p - 1).factorial := by
    rw [ha, Nat.factorial_succ]
    conv_lhs => rw [show p = (p - 1) + 1 by omega, Nat.factorial_succ]
    rw [show p - 1 + 1 = p by omega]
    ring
  have hgg : gg p (aa p) = (Pi3 (aa p) : ℚ) / (((p + 1) * (p - 1).factorial : ℕ) : ℚ) := by
    unfold gg fQ
    rw [Nat.div_self (aa_pos p), pow_one, hfact]
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    push_cast
    field_simp
  have hden : ¬ p ∣ (p + 1) * (p - 1).factorial := by
    rw [Nat.Prime.dvd_mul hp.out, Nat.Prime.dvd_factorial hp.out]
    rintro (h | h)
    · have := (Nat.dvd_add_right (dvd_refl p)).1 h
      exact hp.out.one_lt.ne' (Nat.eq_one_of_dvd_one this) |>.elim
    · omega
  unfold Gr
  rw [hgg, Pint.cast_div_nat (Pint.natCast _) hden, Rat.cast_natCast]
  refine div_ne_zero ?_ ?_
  · rw [Ne, ZMod.natCast_eq_zero_iff, Pi3_eq_sq]
    intro h
    exact A4_not_dvd hp4 (hp.out.dvd_of_dvd_pow h)
  · rw [Ne, ZMod.natCast_eq_zero_iff]; exact hden

/-! ### `W1 ≡ c · smallW` below degree `d = (p+1)/4` -/

/-- The coefficient of `smallW`. -/
noncomputable def wco (p r : ℕ) : ZMod p :=
  ((∏ i ∈ Finset.range r, (4 * (i + 1) - 1) ^ 2 : ℕ) : ZMod p) *
    (((2 * r + 1).factorial : ℕ) : ZMod p)⁻¹

theorem smallW_coeff (r : ℕ) :
    (smallW p).coeff r = if r < (p + 1) / 4 then wco p r else 0 := by
  unfold smallW
  exact RomikPoly.coeff_sum_mono (fun r => wco p r) _ r

theorem fQ_succ (j : ℕ) :
    fQ (j + 1) * (((2 * j + 1) * (2 * j + 2) : ℕ) : ℚ) = fQ j * (((4 * j + 1) ^ 2 : ℕ) : ℚ) := by
  unfold fQ
  have hP : Pi3 (j + 1) = Pi3 j * (4 * j + 1) ^ 2 := by
    unfold Pi3; rw [Finset.prod_range_succ]; congr 2
  have hF : (2 * (j + 1)).factorial = (2 * j).factorial * ((2 * j + 1) * (2 * j + 2)) := by
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]; ring
  rw [hP, hF]
  have h1 : ((2 * j).factorial : ℚ) ≠ 0 := by positivity
  have h2 : (((2 * j + 1) * (2 * j + 2) : ℕ) : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

theorem Gr_ratio (hp4 : p % 4 = 3) (r : ℕ) (hr : r + 1 < (p + 1) / 4) :
    Gr p (aa p + r + 1) * ((2 * r + 2 : ℕ) * (2 * r + 3 : ℕ) : ZMod p) =
      Gr p (aa p + r) * (((4 * r + 3) ^ 2 : ℕ) : ZMod p) := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have ha : 2 * aa p = p + 1 := by unfold aa; omega
  have hK1 : (aa p + r + 1) / aa p = 1 := by
    rw [Nat.div_eq_iff (aa_pos p)]; constructor <;> (unfold aa at *; omega)
  have hK0 : (aa p + r) / aa p = 1 := by
    rw [Nat.div_eq_iff (aa_pos p)]; constructor <;> (unfold aa at *; omega)
  have hq : gg p (aa p + r + 1) * (((2 * (aa p + r) + 1) * (2 * (aa p + r) + 2) : ℕ) : ℚ) =
      gg p (aa p + r) * (((4 * (aa p + r) + 1) ^ 2 : ℕ) : ℚ) := by
    unfold gg
    rw [hK1, hK0, mul_assoc, fQ_succ, mul_assoc]
  have hc : ((gg p (aa p + r + 1) * (((2 * (aa p + r) + 1) * (2 * (aa p + r) + 2) : ℕ) : ℚ) : ℚ) :
      ZMod p) = ((gg p (aa p + r) * (((4 * (aa p + r) + 1) ^ 2 : ℕ) : ℚ) : ℚ) : ZMod p) := by
    rw [hq]
  rw [Pint.cast_mul (gg_pint hp4 _) (Pint.natCast _), Pint.cast_mul (gg_pint hp4 _)
    (Pint.natCast _), Rat.cast_natCast, Rat.cast_natCast] at hc
  unfold Gr
  have e1 : (((2 * (aa p + r) + 1) * (2 * (aa p + r) + 2) : ℕ) : ZMod p) =
      ((2 * r + 2 : ℕ) * (2 * r + 3 : ℕ) : ZMod p) := by
    have : (2 * (aa p + r) + 1) * (2 * (aa p + r) + 2) = (p + (2 * r + 2)) * (p + (2 * r + 3)) := by
      rw [show 2 * (aa p + r) = p + 1 + 2 * r by omega]; ring
    rw [this]; push_cast; rw [ZMod.natCast_self]; ring
  have e2 : (((4 * (aa p + r) + 1) ^ 2 : ℕ) : ZMod p) = (((4 * r + 3) ^ 2 : ℕ) : ZMod p) := by
    have : 4 * (aa p + r) + 1 = 2 * p + (4 * r + 3) := by omega
    rw [this]; push_cast; rw [ZMod.natCast_self]; ring
  rw [← e1, ← e2]
  exact hc

theorem wco_ratio (r : ℕ) (hr : 2 * r + 3 < p) :
    wco p (r + 1) * ((2 * r + 2 : ℕ) * (2 * r + 3 : ℕ) : ZMod p) =
      wco p r * (((4 * r + 3) ^ 2 : ℕ) : ZMod p) := by
  unfold wco
  have hf : (((2 * r + 1).factorial : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff, Nat.Prime.dvd_factorial hp.out]; omega
  have h2 : ((2 * r + 2 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; have := Nat.le_of_dvd (by omega) h; omega
  have h3 : ((2 * r + 3 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; have := Nat.le_of_dvd (by omega) h; omega
  have hF : (2 * (r + 1) + 1).factorial = (2 * r + 1).factorial * ((2 * r + 2) * (2 * r + 3)) := by
    rw [show 2 * (r + 1) + 1 = 2 * r + 1 + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    ring
  rw [Finset.prod_range_succ, hF, show 4 * (r + 1) - 1 = 4 * r + 3 by omega, Nat.cast_mul,
    Nat.cast_mul, Nat.cast_mul, mul_inv, mul_inv]
  have hA := mul_inv_cancel₀ h2
  have hB := mul_inv_cancel₀ h3
  set P := ((∏ i ∈ Finset.range r, (4 * (i + 1) - 1) ^ 2 : ℕ) : ZMod p)
  set Q := (((4 * r + 3) ^ 2 : ℕ) : ZMod p)
  set F := (((2 * r + 1).factorial : ℕ) : ZMod p)
  set A := ((2 * r + 2 : ℕ) : ZMod p)
  set B := ((2 * r + 3 : ℕ) : ZMod p)
  linear_combination (P * Q * F⁻¹ * B * B⁻¹) * hA + (P * Q * F⁻¹) * hB

theorem Gr_eq_wco (hp4 : p % 4 = 3) (r : ℕ) (hr : r < (p + 1) / 4) :
    Gr p (aa p + r) = Gr p (aa p) * wco p r := by
  induction r with
  | zero => simp [wco]
  | succ r ih =>
    have h1 := Gr_ratio hp4 r hr
    have h2 := wco_ratio (p := p) r (by omega)
    have hX : ((2 * r + 2 : ℕ) * (2 * r + 3 : ℕ) : ZMod p) ≠ 0 := by
      refine mul_ne_zero ?_ ?_ <;> rw [Ne, ZMod.natCast_eq_zero_iff] <;> intro h <;>
        have := Nat.le_of_dvd (by omega) h <;> omega
    rw [ih (by omega)] at h1
    apply mul_right_cancel₀ hX
    rw [show aa p + (r + 1) = aa p + r + 1 by ring, h1, mul_assoc, ← h2]
    ring

theorem W1_pow_coeff (hp4 : p % 4 = 3) (r : ℕ) (hr : r < (p + 1) / 4) :
    ((RomikPoly.W1 (Gr p)) ^ ((p + 1) / 2)).coeff r =
      Gr p (aa p) ^ ((p + 1) / 2) * ((smallW p) ^ ((p + 1) / 2)).coeff r := by
  have hdvd : (X : (ZMod p)[X]) ^ ((p + 1) / 4) ∣ RomikPoly.W1 (Gr p) - C (Gr p (aa p)) * smallW p := by
    rw [X_pow_dvd_iff]
    intro s hs
    rw [coeff_sub, coeff_C_mul, smallW_coeff, RomikPoly.W1_coeff]
    have hsa : s < (p + 1) / 2 := by omega
    simp only [hsa, hs, ↓reduceIte]
    rw [Gr_eq_wco hp4 s hs, sub_self]
  have h2 := hdvd.trans (sub_dvd_pow_sub_pow (RomikPoly.W1 (Gr p)) (C (Gr p (aa p)) * smallW p)
    ((p + 1) / 2))
  rw [X_pow_dvd_iff] at h2
  have := h2 r hr
  rw [coeff_sub, sub_eq_zero, mul_pow, ← C_pow, coeff_C_mul] at this
  exact this

end Romik
```

### `RomikMain.lean`

```lean
import RomikLink
import RomikArith
import RomikValues
import Mathlib.Tactic.NormNum.Prime

/-!
# MathDB 358162: Krattenthaler–Müller, arXiv:2304.11471 (v4), Conjecture 44

For a prime `p ≡ 3 (mod 4)`:
* (odd clause, exactly as printed) if `e` is odd, `p^e ∣ v(n)` for `n ≥ (ep+2)(p+1)/4`;
* (even clause, exact classification of the exceptions) if `e > 0` is even and `n ≥ ⌈ep²/4⌉`,
  `p^e ∤ v(n)` iff `e = (p+1)(2j+1)` with `2j < p-1` and `4n = ep² + (p+1) + 4r` with
  `4r < p+1` and `[T^r] smallW_p(T)^((p+1)/2) ≠ 0` in `F_p[T]`.
-/

open Finset Polynomial

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Romik

variable {p : ℕ} [hp : Fact p.Prime]

theorem p_ne_two (hp4 : p % 4 = 3) : p ≠ 2 := by
  intro h; rw [h] at hp4; norm_num at hp4

/-- The residues are the coefficients of the explicit square root `E_M`. -/
theorem D_eq_co (hp4 : p % 4 = 3) (M n : ℕ) (hn : n / aa p < p ^ (M + 1)) :
    D p n = RomikPoly.co (RomikPoly.EE (Gr p) M) (n / aa p) (n % aa p) :=
  RomikPoly.main (Gr p) (p_ne_two hp4) Gr_zero (fun j hj => gg_red_zero hp4 j hj) (D p) D_zero
    (fun j hj => noCarry_rec hp4 j hj) M n hn

theorem choose_ne_zero_mod {h j : ℕ} (hh : h < p) (hj : j ≤ h) : ((Nat.choose h j : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd
  have h1 : Nat.choose h j ∣ h.factorial := by
    have := Nat.choose_mul_factorial_mul_factorial hj
    exact ⟨j.factorial * (h - j).factorial, by rw [← this]; ring⟩
  have := (Nat.Prime.dvd_factorial hp.out).1 (hd.trans h1)
  omega

end Romik

/-- **Conjecture 44 (1), the odd clause.** -/
theorem romik_conj44_odd {p e n : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3)
    (he : Odd e) (hn : (e * p + 2) * (p + 1) ≤ 4 * n) : (p : ℤ) ^ e ∣ romikV n := by
  have := Fact.mk hp
  rcases RomikArith.odd_arith hp4 he hn with h | ⟨h, hK⟩
  · exact Romik.link_ge hp4 n e h
  · apply Romik.link_red hp4 n e h
    have hKM : n / Romik.aa p < p ^ (n / Romik.aa p + 1) :=
      lt_trans (Nat.lt_succ_self _) (Nat.lt_pow_self hp.one_lt)
    rw [Romik.D_eq_co hp4 _ n hKM]
    exact RomikPoly.co_EE_eq_zero (Romik.Gr p) (Romik.p_ne_two hp4) _ _ _ hK

/-- The even clause holds up to one factor of `p`: `p^(e-1) ∣ v(n)`. -/
theorem romik_conj44_even_lower {p e n : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3)
    (he : Even e) (hn : e * p ^ 2 ≤ 4 * n) : (p : ℤ) ^ (e - 1) ∣ romikV n := by
  have := Fact.mk hp
  rcases Nat.eq_zero_or_pos e with rfl | he0
  · simp
  have := RomikArith.even_lower hp4 he hn
  exact Romik.link_ge hp4 n (e - 1) (by unfold Romik.aa; omega)

/-- **Conjecture 44 (2), the even clause: exact classification of the exceptions.** -/
theorem romik_conj44_even_exact {p e n : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3)
    (he0 : 0 < e) (he : Even e) (hn : e * p ^ 2 ≤ 4 * n) :
    ¬ (p : ℤ) ^ e ∣ romikV n ↔ ∃ j r, 2 * j < p - 1 ∧ e = (p + 1) * (2 * j + 1) ∧ 4 * r < p + 1 ∧
        ((smallW p) ^ ((p + 1) / 2)).coeff r ≠ 0 ∧ 4 * n = e * p ^ 2 + (p + 1) + 4 * r := by
  have := Fact.mk hp
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hlow := RomikArith.even_lower hp4 he hn
  have hp2 := Romik.p_ne_two hp4
  constructor
  · intro hnd
    have hlt : padicValNat p (2 * n).factorial < n / ((p + 1) / 2) + e := by
      by_contra h
      exact hnd (Romik.link_ge hp4 n e (by unfold Romik.aa; omega))
    have hD : Romik.D p n ≠ 0 := fun hD => hnd (Romik.link_red hp4 n e hlow hD)
    obtain ⟨hK3, hdig⟩ := RomikArith.even_conf hp4 he hn hlt
    rw [Romik.D_eq_co hp4 2 n (by unfold Romik.aa; simpa using hK3),
      RomikPoly.co_EE_two _ hp2] at hD
    unfold Romik.aa at hD
    have c0 : n / ((p + 1) / 2) % p ≤ (p + 1) / 2 := by
      by_contra h
      apply hD
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
    have c1 : n / ((p + 1) / 2) / p % p ≤ (p - 1) / 2 := by
      by_contra h
      apply hD
      rw [Nat.choose_eq_zero_of_lt (n := (p - 1) / 2) (by omega)]
      simp
    have c2 : n / ((p + 1) / 2) / p / p ≤ (p - 1) / 2 := by
      by_contra h
      apply hD
      rw [Nat.choose_eq_zero_of_lt (n := (p - 1) / 2) (k := n / ((p + 1) / 2) / p / p) (by omega)]
      simp
    obtain ⟨d0, -, hj, hej, hr, h4n⟩ := hdig c0 c1 c2
    refine ⟨n / ((p + 1) / 2) / p / p, n % ((p + 1) / 2), hj, hej, hr, ?_, h4n⟩
    rw [d0, Nat.sub_self, pow_zero, mul_one] at hD
    intro hc
    apply hD
    have hR : n % ((p + 1) / 2) < (p + 1) / 4 := by omega
    have := Romik.W1_pow_coeff hp4 _ hR
    unfold Romik.aa at this
    rw [this, hc, mul_zero, mul_zero]
  · rintro ⟨j, r, hj, hej, hr, hc, h4n⟩
    obtain ⟨hK, hR, hν⟩ := RomikArith.even_conv hp4 hj hej hr h4n
    apply Romik.link_not hp4 n e (by omega) hν
    have ha : (p + 1) / 2 < p := by omega
    have hh : (p - 1) / 2 < p := by omega
    have hjp : j < p := by omega
    have hd1 : (p * p * j + p * ((p - 1) / 2) + (p + 1) / 2) / p = p * j + (p - 1) / 2 ∧
        (p * p * j + p * ((p - 1) / 2) + (p + 1) / 2) % p = (p + 1) / 2 :=
      (Nat.div_mod_unique hp.pos).2 ⟨by ring, ha⟩
    have hd2 : (p * j + (p - 1) / 2) / p = j ∧ (p * j + (p - 1) / 2) % p = (p - 1) / 2 :=
      (Nat.div_mod_unique hp.pos).2 ⟨by ring, hh⟩
    have hK3 : n / Romik.aa p < p ^ (2 + 1) := by
      unfold Romik.aa
      rw [hK]
      have h1 := Nat.mul_le_mul_left (p * p) (Nat.succ_le_of_lt hjp)
      rw [Nat.mul_succ] at h1
      have h2 := Nat.mul_le_mul_left p (Nat.succ_le_of_lt hh)
      rw [Nat.mul_succ] at h2
      have h3 : p ^ (2 + 1) = p * p * p := by ring
      omega
    rw [Romik.D_eq_co hp4 2 n hK3, RomikPoly.co_EE_two _ hp2]
    unfold Romik.aa
    rw [hK, hR, hd1.1, hd1.2, hd2.1, hd2.2, Nat.choose_self, Nat.choose_self, Nat.sub_self,
      pow_zero, mul_one]
    have hW := Romik.W1_pow_coeff hp4 r (by omega)
    unfold Romik.aa at hW
    rw [hW]
    have hc0 := Romik.Gr_a_ne hp4
    unfold Romik.aa at hc0
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by simp) ?_) ?_) (mul_ne_zero (pow_ne_zero _ hc0) hc)
    · exact mul_ne_zero (pow_ne_zero _ hc0) (by simp)
    · exact mul_ne_zero (pow_ne_zero _ hc0) (Romik.choose_ne_zero_mod hh (by omega))

/-! ## Sanity guards and vacuity checks -/

theorem coeff_one_pow {R : Type*} [CommSemiring R] (f : R[X]) (hf : f.coeff 0 = 1) (n : ℕ) :
    (f ^ n).coeff 1 = n * f.coeff 1 := by
  induction n with
  | zero => simp [coeff_one]
  | succ n ih =>
    rw [pow_succ, coeff_mul, Finset.Nat.antidiagonal_succ]
    simp only [Finset.Nat.antidiagonal_zero, Finset.sum_cons, Finset.sum_map,
      Finset.sum_singleton, Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk,
      Prod.map, Nat.succ_eq_add_one, zero_add, id]
    rw [ih, coeff_zero_eq_eval_zero (f ^ n), eval_pow, ← coeff_zero_eq_eval_zero, hf, one_pow]
    push_cast
    simp only [id_eq, hf]
    ring

theorem smallW_seven_coeff : ((smallW 7) ^ ((7 + 1) / 2)).coeff 1 ≠ 0 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h0 : (smallW 7).coeff 0 = 1 := by rw [Romik.smallW_coeff]; simp [Romik.wco]
  rw [coeff_one_pow _ h0, Romik.smallW_coeff]
  simp only [show (1 : ℕ) < (7 + 1) / 4 by norm_num, ↓reduceIte, Romik.wco]
  exact mul_ne_zero (by rw [Ne, ZMod.natCast_eq_zero_iff]; decide)
    (mul_ne_zero (by rw [Ne, ZMod.natCast_eq_zero_iff]; decide)
      (inv_ne_zero (by rw [Ne, ZMod.natCast_eq_zero_iff]; decide)))

/-- Sanity guard (the source's own data point `(p,e) = (7,8)`, corrected bound `102`). -/
theorem romikV_seven_eight : (7 : ℤ) ^ 8 ∣ romikV 102 ∧ ¬ (7 : ℤ) ^ 8 ∣ romikV 101 := by
  have h7 : Nat.Prime 7 := by norm_num
  constructor
  · by_contra h
    obtain ⟨j, r, -, hej, hr, -, h4n⟩ :=
      (romik_conj44_even_exact (n := 102) h7 (by norm_num) (by norm_num) ⟨4, rfl⟩ (by norm_num)).1
        (by exact_mod_cast h)
    omega
  · have := (romik_conj44_even_exact (n := 101) h7 (by norm_num) (by norm_num) ⟨4, rfl⟩
      (by norm_num)).2 ⟨0, 1, by norm_num, by norm_num, by norm_num, smallW_seven_coeff,
        by norm_num⟩
    exact_mod_cast this

/-- Vacuity check: the odd hypotheses are satisfiable (`p = 3`, `e = 1`, `n = 5`). -/
theorem romik_odd_hyp_satisfiable :
    ∃ p e n : ℕ, p.Prime ∧ p % 4 = 3 ∧ Odd e ∧ (e * p + 2) * (p + 1) ≤ 4 * n :=
  ⟨3, 1, 5, by norm_num, by norm_num, ⟨0, rfl⟩, by norm_num⟩

/-- Vacuity check: the even hypotheses hold with the right-hand side of the iff true
(`p = 7`, `e = 8`, `n = 101`), and also with it false (`n = 102`). -/
theorem romik_even_iff_both_sides :
    (∃ j r, 2 * j < 7 - 1 ∧ 8 = (7 + 1) * (2 * j + 1) ∧ 4 * r < 7 + 1 ∧
        ((smallW 7) ^ ((7 + 1) / 2)).coeff r ≠ 0 ∧ 4 * 101 = 8 * 7 ^ 2 + (7 + 1) + 4 * r) ∧
    ¬ (∃ j r, 2 * j < 7 - 1 ∧ 8 = (7 + 1) * (2 * j + 1) ∧ 4 * r < 7 + 1 ∧
        ((smallW 7) ^ ((7 + 1) / 2)).coeff r ≠ 0 ∧ 4 * 102 = 8 * 7 ^ 2 + (7 + 1) + 4 * r) := by
  refine ⟨⟨0, 1, by norm_num, by norm_num, by norm_num, smallW_seven_coeff, by norm_num⟩, ?_⟩
  rintro ⟨j, r, -, -, hr, -, h4n⟩
  omega

#print axioms romik_conj44_odd
#print axioms romik_conj44_even_exact
#print axioms romik_conj44_even_lower
#print axioms romikQ_int
#print axioms romikV_printed_values
#print axioms romikV_10_not_dvd
#print axioms romikV_seven_eight
#print axioms romik_odd_hyp_satisfiable
#print axioms romik_even_iff_both_sides
```

