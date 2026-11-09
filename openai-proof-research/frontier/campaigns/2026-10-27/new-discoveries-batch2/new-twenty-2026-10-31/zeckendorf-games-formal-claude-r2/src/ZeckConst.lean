/-
  Part (b) of MathDB 347063: the constant `c = 5/2 - phi + ∑_{j≥2} 1/F_{2j}`, as a tsum,
  and the bracket `1.206 < c < 1.207`.
-/
import ZeckLevel
import Mathlib.Analysis.SpecificLimits.Basic

open Classical

set_option linter.unusedSimpArgs false

namespace Zeck

/-- The reciprocals of the even-indexed Fibonacci numbers `F_{2i+4}`. -/
noncomputable def aT (i : ℕ) : ℝ := 1 / (F (2 * i + 4) : ℝ)

/-- Partial sums of the series. -/
noncomputable def Ssum (j : ℕ) : ℝ := ∑ i ∈ Finset.range j, aT i

/-- The constant of the Combine Smallest theorem. -/
noncomputable def combC : ℝ := 5 / 2 - phi + ∑' j : ℕ, 1 / (F (2 * (j + 2)) : ℝ)

lemma F_cast_pos (i : ℕ) : (0 : ℝ) < (F i : ℝ) := by
  exact_mod_cast F_pos i

lemma aT_pos (i : ℕ) : 0 < aT i := by
  unfold aT
  have := F_cast_pos (2 * i + 4)
  positivity

lemma aT_nonneg (i : ℕ) : 0 ≤ aT i := le_of_lt (aT_pos i)

lemma Ssum_zero : Ssum 0 = 0 := by simp [Ssum]

lemma Ssum_succ (j : ℕ) : Ssum (j + 1) = Ssum j + aT j := by
  simp [Ssum, Finset.sum_range_succ]

lemma F_double_le (i : ℕ) : 2 * F (2 * i + 4) ≤ F (2 * i + 6) := by
  have h1 : F (2 * i + 6) = F (2 * i + 5) + F (2 * i + 4) := by
    have := F_rec (i := 2 * i + 5) (by omega)
    simpa using this
  have h2 : F (2 * i + 4) ≤ F (2 * i + 5) := F_mono (by omega)
  omega

lemma aT_succ_le (i : ℕ) : aT (i + 1) ≤ aT i / 2 := by
  unfold aT
  have e : 2 * (i + 1) + 4 = 2 * i + 6 := by ring
  rw [e]
  have h1 := F_double_le i
  have h2 : (2 : ℝ) * (F (2 * i + 4) : ℝ) ≤ (F (2 * i + 6) : ℝ) := by exact_mod_cast h1
  have h3 := F_cast_pos (2 * i + 4)
  have h4 := F_cast_pos (2 * i + 6)
  rw [div_div, div_le_div_iff₀ h4 (by positivity)]
  linarith

lemma aT_geo (J t : ℕ) : aT (J + t) ≤ aT J * (1 / 2 : ℝ) ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h1 := aT_succ_le (J + t)
    rw [show J + (t + 1) = (J + t) + 1 by ring, pow_succ]
    nlinarith

lemma aT_summable : Summable aT := by
  have hg : Summable (fun t : ℕ => aT 0 * (1 / 2 : ℝ) ^ t) := summable_geometric_two.mul_left _
  refine Summable.of_nonneg_of_le aT_nonneg (fun t => ?_) hg
  have h := aT_geo 0 t
  simpa using h

lemma aT_split (J : ℕ) : ∑' i, aT i = Ssum J + ∑' t, aT (t + J) :=
  (aT_summable.sum_add_tsum_nat_add J).symm

lemma aT_tail_le (J : ℕ) : ∑' t, aT (t + J) ≤ 2 * aT J := by
  have hsum : Summable (fun t => aT (t + J)) := (summable_nat_add_iff J).2 aT_summable
  have hg : Summable (fun t : ℕ => aT J * (1 / 2 : ℝ) ^ t) := summable_geometric_two.mul_left _
  have hle : ∀ t, aT (t + J) ≤ aT J * (1 / 2 : ℝ) ^ t := by
    intro t
    rw [add_comm]
    exact aT_geo J t
  calc ∑' t, aT (t + J) ≤ ∑' t : ℕ, aT J * (1 / 2 : ℝ) ^ t := hsum.tsum_le_tsum hle hg
    _ = aT J * 2 := by rw [tsum_mul_left, tsum_geometric_two]
    _ = 2 * aT J := by ring

lemma aT_tail_nonneg (J : ℕ) : 0 ≤ ∑' t, aT (t + J) := by
  exact tsum_nonneg (fun t => aT_nonneg _)

lemma combC_eq : combC = 5 / 2 - phi + ∑' i, aT i := by
  unfold combC
  congr 1

lemma phi_lt : phi < 1.6181 := by
  unfold phi
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

lemma phi_gt : 1.618 < phi := by
  unfold phi
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

/-- The bracket of Conjecture 1.4 for the Combine Smallest constant. -/
theorem combC_bracket : (1.206 : ℝ) < combC ∧ combC < 1.207 := by
  have hphi1 := phi_lt
  have hphi2 := phi_gt
  have hS7 : Ssum 7 = 1 / 5 + 1 / 13 + 1 / 34 + 1 / 89 + 1 / 233 + 1 / 610 + 1 / 1597 := by
    simp only [Ssum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, aT]
    have e0 : F (2 * 0 + 4) = 5 := by decide
    have e1 : F (2 * 1 + 4) = 13 := by decide
    have e2 : F (2 * 2 + 4) = 34 := by decide
    have e3 : F (2 * 3 + 4) = 89 := by decide
    have e4 : F (2 * 4 + 4) = 233 := by decide
    have e5 : F (2 * 5 + 4) = 610 := by decide
    have e6 : F (2 * 6 + 4) = 1597 := by decide
    rw [e0, e1, e2, e3, e4, e5, e6]
    norm_num
  have ha7 : aT 7 = 1 / 4181 := by
    unfold aT
    have e7 : F (2 * 7 + 4) = 4181 := by decide
    rw [e7]
    norm_num
  have hsplit := aT_split 7
  have htail := aT_tail_le 7
  have hnn := aT_tail_nonneg 7
  rw [combC_eq, hsplit, hS7]
  rw [ha7] at htail
  constructor
  · norm_num at *
    linarith
  · norm_num at *
    linarith

end Zeck
