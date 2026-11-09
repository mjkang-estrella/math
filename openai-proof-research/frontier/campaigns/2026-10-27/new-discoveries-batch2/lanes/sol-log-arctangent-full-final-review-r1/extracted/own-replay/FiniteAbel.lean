import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option warningAsError true
namespace LogArctangentMean
/-- Abel identity with the prefix stored before each coefficient. -/
theorem finiteAbel (c w : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, c i * w i) =
    (∑ i ∈ Finset.range n, c i) * w n +
    ∑ i ∈ Finset.range n, (∑ j ∈ Finset.range (i+1), c j) * (w i-w (i+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ] at ih ⊢
    rw [ih]
    ring
theorem finiteAbel_nonneg (c w : ℕ → ℝ) (n : ℕ)
    (hp : ∀ k ≤ n, 0 ≤ ∑ i ∈ Finset.range k, c i)
    (hw : 0 ≤ w n) (hd : ∀ i < n, w (i+1) ≤ w i) :
    0 ≤ ∑ i ∈ Finset.range n, c i * w i := by
  rw [finiteAbel]
  exact add_nonneg (mul_nonneg (hp n le_rfl) hw)
    (Finset.sum_nonneg fun i hi => mul_nonneg
      (hp (i+1) (Nat.succ_le_of_lt (Finset.mem_range.mp hi)))
      (sub_nonneg.mpr (hd i (Finset.mem_range.mp hi))))
theorem finiteAbel_pos (c w : ℕ → ℝ) (n : ℕ)
    (hp : ∀ k ≤ n, 0 ≤ ∑ i ∈ Finset.range k, c i)
    (hs : 0 < ∑ i ∈ Finset.range n, c i)
    (hw : 0 < w n) (hd : ∀ i < n, w (i+1) ≤ w i) :
    0 < ∑ i ∈ Finset.range n, c i * w i := by
  rw [finiteAbel]
  exact add_pos_of_pos_of_nonneg (mul_pos hs hw)
    (Finset.sum_nonneg fun i hi => mul_nonneg
      (hp (i+1) (Nat.succ_le_of_lt (Finset.mem_range.mp hi)))
      (sub_nonneg.mpr (hd i (Finset.mem_range.mp hi))))
end LogArctangentMean
