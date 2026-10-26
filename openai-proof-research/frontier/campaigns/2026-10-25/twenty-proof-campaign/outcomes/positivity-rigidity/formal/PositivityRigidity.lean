import Mathlib

namespace PositivityRigidity
open scoped BigOperators

/-- The finite sum in the printed source assertion. -/
def sourceSum (s k : ℕ) (q qt : ℝ) (p : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.range (min k s + 1),
    (Nat.choose (s - 1 + k - m) (s - 1) : ℝ) * p m * q^m * (-qt)^(k-m)

def Hypotheses (s : ℕ) (q qt : ℝ) (p : ℕ → ℝ) : Prop :=
  0 < s ∧ q ≠ 0 ∧ 0 < qt ∧ ∀ k, k ≤ s + 1 → 0 ≤ sourceSum s k q qt p

def Conclusion (s : ℕ) (q qt : ℝ) (p : ℕ → ℝ) : Prop :=
  0 ≤ p 0 ∧ (∀ m, 1 ≤ m → m ≤ s + 1 →
    p m = p 0 * (Nat.choose s m : ℝ) * (qt/q)^m) ∧
    sourceSum s 0 q qt p = p 0 ∧
    ∀ k, 1 ≤ k → k ≤ s + 1 → sourceSum s k q qt p = 0

def coefficients (t : ℝ) (m : ℕ) : ℝ := if m = 2 then t else 1

/-- The endpoint coefficient is absent from every premise. -/
theorem sum_ignores_endpoint (s k : ℕ) (q qt : ℝ) (p : ℕ → ℝ) (t : ℝ) :
    sourceSum s k q qt (Function.update p (s+1) t) = sourceSum s k q qt p := by
  unfold sourceSum
  apply Finset.sum_congr rfl
  intro m hm
  have hms : m ≤ s := by
    have h := Finset.mem_range.mp hm
    have hmin := min_le_right k s
    omega
  have hne : m ≠ s + 1 := by omega
  rw [Function.update_of_ne hne]

theorem candidate_hypotheses (t : ℝ) : Hypotheses 1 1 1 (coefficients t) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro k hk
  interval_cases k <;> norm_num [sourceSum, coefficients, Finset.sum_range_succ]

theorem candidate_not_conclusion (t : ℝ) (ht : t ≠ 0) :
    ¬ Conclusion 1 1 1 (coefficients t) := by
  intro h
  have he := h.2.1 2 (by norm_num) (by norm_num)
  norm_num [coefficients] at he
  exact ht he

/-- A whole nonzero family refutes the statement exactly as printed. -/
theorem printed_conjecture_false :
    ¬ (∀ (s : ℕ) (q qt : ℝ) (p : ℕ → ℝ), Hypotheses s q qt p →
      Conclusion s q qt p) := by
  intro h
  exact candidate_not_conclusion 1 (by norm_num) (h 1 1 1 (coefficients 1) (candidate_hypotheses 1))

end PositivityRigidity
