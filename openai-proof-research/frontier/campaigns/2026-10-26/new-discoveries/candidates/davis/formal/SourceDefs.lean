import Mathlib

namespace Davis

noncomputable section

def falling (x : ℝ) (i : ℕ) : ℝ := ∏ j ∈ Finset.range i, (x - j)

def weight (d i : ℕ) (x : ℝ) : ℝ :=
  (falling x i) ^ 2 * (falling x (d - i)) ^ 2 /
    ((Nat.factorial i : ℝ) * (Nat.factorial (d - i) : ℝ))

def P (d : ℕ) (x : ℝ) : ℝ := ∑ i ∈ Finset.range (d + 1), weight d i x

def quotient (d : ℕ) (x : ℝ) : ℝ :=
  2 / (d + 1 : ℝ) * x ^ 2 - 2 * d / (d + 1 : ℝ) * x + d / 2

def remainder (d : ℕ) (x : ℝ) : ℝ := P (d + 1) x - quotient d x * P d x

def SourceConjecture319187 : Prop := ∀ (d : ℕ) (x : ℝ), 5 ≤ d →
  ((d : ℝ) + Real.sqrt (d + 2)) / 2 ≤ x →
  -remainder d x / P d x ≥ (199 / 200 : ℝ) * (d - 2) / (2 * x + d - 2)

theorem falling_pos {x : ℝ} {n : ℕ} (h : ∀ j < n, (j : ℝ) < x) :
    0 < falling x n := by
  unfold falling
  apply Finset.prod_pos
  intro j hj
  exact sub_pos.mpr (h j (Finset.mem_range.mp hj))

theorem weight_nonneg (d i : ℕ) (x : ℝ) : 0 ≤ weight d i x := by
  unfold weight
  positivity

theorem P_pos {d : ℕ} {x : ℝ} (hx : (d : ℝ) / 2 < x) : 0 < P d x := by
  have hl : 0 < falling x (d / 2) := by
    apply falling_pos
    intro j hj
    have hjd : 2 * j < d := by omega
    have hjdr : (2 : ℝ) * j < d := by exact_mod_cast hjd
    linarith
  have hr : 0 < falling x (d - d / 2) := by
    apply falling_pos
    intro j hj
    have hjd : 2 * j < d := by omega
    have hjdr : (2 : ℝ) * j < d := by exact_mod_cast hjd
    linarith
  unfold P
  apply Finset.sum_pos'
  · intro i hi
    exact weight_nonneg d i x
  · refine ⟨d / 2, Finset.mem_range.mpr (by omega), ?_⟩
    unfold weight
    positivity

end

end Davis
