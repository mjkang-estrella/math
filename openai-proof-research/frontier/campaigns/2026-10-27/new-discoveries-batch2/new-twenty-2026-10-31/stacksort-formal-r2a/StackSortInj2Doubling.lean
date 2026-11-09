import StackSortFinal
import Mathlib.Data.Nat.Choose.Basic
namespace StackSort
open BigOperators
noncomputable section
/-- The factorial conversion does not assume the real inequality. -/
theorem doubling_of_injection (h : DoublingInjection) : Doubling := by
  intro a
  have hc : Nat.choose (2*a) a * a.factorial * a.factorial = (2*a).factorial := by
    simpa [show 2*a-a=a by omega] using
      (Nat.choose_mul_factorial_mul_factorial (n := 2*a) (k := a) (by omega))
  have hcr : (Nat.choose (2*a) a : ℝ) * (a.factorial : ℝ) * (a.factorial : ℝ) =
      ((2*a).factorial : ℝ) := by exact_mod_cast hc
  have hi : (Nat.choose (2*a) a : ℝ) * (P a : ℝ)^2 ≤ (P (2*a+1) : ℝ) := by
    exact_mod_cast h a
  have hf : (0 : ℝ) < (a.factorial : ℝ) := by positivity
  have hf2 : (0 : ℝ) < ((2*a).factorial : ℝ) := by positivity
  have hn : (0 : ℝ) < 2*(a : ℝ)+1 := by positivity
  unfold deg
  rw [div_pow, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_mul]
  norm_num only [Nat.cast_ofNat, Nat.cast_one]
  have he : (2*(a:ℝ)+1) * ((P (2*a+1):ℝ) / ((2*(a:ℝ)+1)*((2*a).factorial:ℝ))) =
      (P (2*a+1):ℝ) / ((2*a).factorial:ℝ) := by field_simp
  rw [he]
  apply (div_le_div_iff₀ (sq_pos_of_pos hf) hf2).mpr
  calc
    _ = (Nat.choose (2*a) a : ℝ) * (P a : ℝ)^2 * (a.factorial : ℝ)^2 := by
      rw [← hcr]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hi (sq_nonneg _)
end
end StackSort
