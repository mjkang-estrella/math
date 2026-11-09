import UpperCounts
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace WheelFormal
attribute [local instance] Classical.propDecidable

theorem family1_rim_count (t : ℕ) (i j : ZMod (2*t+1)) :
    (∑ a, ∑ b, ∑ c : Fin 2,
      if (some i,some j) ∈ family1 t a b c then (1:ℝ) else 0) = 4*(t:ℝ)^2 := by
  classical
  have he : ∀ a b : ZMod (2*t+1),
      (∑ c : Fin 2, if (some i,some j) ∈ family1 t a b c then (1:ℝ) else 0) =
      (if i = a then 0 else 1)*(if j = b then 0 else 1) := by
    intro a b
    simp only [family1,profileFamily,Finset.mem_filter,Finset.mem_univ,true_and,
      Fin.sum_univ_two,Fin.val_zero,Fin.val_one]
    have hh : ((i-a-1).val+(j-b-1).val)%2 < 2 := Nat.mod_lt _ (by decide)
    by_cases ha : i = a <;> by_cases hb : j = b <;> simp [ha,hb]
    rcases (show ((i-a-1).val+(j-b-1).val)%2 = 0 ∨
      ((i-a-1).val+(j-b-1).val)%2 = 1 by omega) with h | h <;> simp [h]
  simp_rw [he,← Finset.mul_sum]
  have hf : ∀ x : ZMod (2*t+1), (∑ a, if x = a then (0:ℝ) else 1) = 2*t := by
    intro x
    have hh : (∑ a : ZMod (2*t+1), if x = a then (0:ℝ) else 1) =
        (∑ _a : ZMod (2*t+1), (1:ℝ)) - ∑ a, if x = a then (1:ℝ) else 0 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> norm_num
    rw [hh]
    have hxsum : (∑ a : ZMod (2*t+1), if x = a then (1:ℝ) else 0) = 1 := by simp
    rw [hxsum]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,Finset.sum_const,
      Finset.card_univ,ZMod.card,nsmul_eq_mul,mul_one]
    push_cast
    ring
  rw [hf,← Finset.sum_mul,hf]
  ring

theorem family2_mixedA_count (t : ℕ) (i : ZMod (2*t+1)) :
    (∑ a, ∑ b : ZMod (2*t+1),
      if (some i,none) ∈ family2 t a b then (1:ℝ) else 0) = (t:ℝ)*(2*t+1) := by
  classical
  simp only [family2,profileFamily,Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]
  rw [← Finset.mul_sum,alternating_fibre]
  push_cast
  ring

theorem family2_mixedB_count (t : ℕ) (j : ZMod (2*t+1)) :
    (∑ a, ∑ b : ZMod (2*t+1),
      if (none,some j) ∈ family2 t a b then (1:ℝ) else 0) = (t:ℝ)*(2*t+1) := by
  classical
  simp only [family2,profileFamily,Finset.mem_filter,Finset.mem_univ,true_and,
    alternating_fibre,Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]
  push_cast
  ring
end WheelFormal
