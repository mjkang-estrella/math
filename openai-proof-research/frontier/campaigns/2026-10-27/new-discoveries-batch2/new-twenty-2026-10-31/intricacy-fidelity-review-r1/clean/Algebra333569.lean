import Target333569

namespace MathDB333569
noncomputable section

/-- The eigenvalue/stationary-bias chart used in the ordinary proof. -/
def chart (l t : ℝ) : ℝ × ℝ :=
  (1 - (1-l)*(1-t)/2, 1 - (1-l)*(1+t)/2)
def pi (t : ℝ) (a : Fin 2) : ℝ := if a = 0 then (1+t)/2 else (1-t)/2
def kernel (l t : ℝ) (a b : Fin 2) : ℝ :=
  l * (if a = b then 1 else 0) + (1-l) * pi t b

theorem chart_trans (l t : ℝ) (a b : Fin 2) :
    trans (chart l t) a b = kernel l t a b := by
  fin_cases a <;> fin_cases b <;> norm_num [trans, chart, kernel, pi] <;> ring

theorem pi_sum (t : ℝ) : ∑ a : Fin 2, pi t a = 1 := by
  simp [Fin.sum_univ_two, pi]
  ring

theorem kernel_sum (l t : ℝ) (a : Fin 2) : ∑ b : Fin 2, kernel l t a b = 1 := by
  fin_cases a <;> simp [Fin.sum_univ_two, kernel, pi] <;> ring

theorem pi_invariant (l t : ℝ) (b : Fin 2) :
    (∑ a : Fin 2, pi t a * kernel l t a b) = pi t b := by
  fin_cases b <;> simp [Fin.sum_univ_two, kernel, pi] <;> ring

theorem kernel_comp (l r t : ℝ) (a b : Fin 2) :
    (∑ c : Fin 2, kernel l t a c * kernel r t c b) = kernel (l*r) t a b := by
  fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_two, kernel, pi] <;> ring

/-- Iterated transitions, including the zero-step identity. -/
def steps (l t : ℝ) : ℕ → Fin 2 → Fin 2 → ℝ
  | 0, a, b => if a = b then 1 else 0
  | n+1, a, b => ∑ c : Fin 2, steps l t n a c * kernel l t c b

theorem steps_eq (l t : ℝ) (n : ℕ) (a b : Fin 2) :
    steps l t n a b = kernel (l^n) t a b := by
  induction n generalizing a b with
  | zero => simp [steps, kernel]
  | succ n ih => simp_rw [steps, ih, kernel_comp, pow_succ]

theorem chart_mem_interior {l t : ℝ} (hl : 0 < l) (hl1 : l < 1)
    (ht : -1 < t) (ht1 : t < 1) : chart l t ∈ interior := by
  have h₁ := mul_pos (by linarith : 0 < 1-l) (by linarith : 0 < 1-t)
  have h₂ := mul_pos (by linarith : 0 < 1-l) (by linarith : 0 < 1+t)
  have h₃ : (1-l)*(1-t) < 2 := by nlinarith [mul_pos hl (by linarith : 0 < 1-t)]
  have h₄ : (1-l)*(1+t) < 2 := by nlinarith [mul_pos hl (by linarith : 0 < 1+t)]
  change 0 < 1-(1-l)*(1-t)/2 ∧ _ ∧ _ ∧ _
  dsimp [chart]
  constructor; · linarith
  constructor; · linarith
  constructor <;> linarith

theorem chart_stationary {l : ℝ} (hl : l ≠ 1) (t : ℝ) (a : Fin 2) :
    stationary (chart l t) a = pi t a := by
  have hd : 2-(chart l t).1-(chart l t).2 = 1-l := by dsimp [chart]; ring
  have hn : 1-l ≠ 0 := sub_ne_zero.mpr (Ne.symm hl)
  fin_cases a <;> simp only [stationary, Fin.isValue, pi] <;>
    rw [hd] <;> dsimp [chart] <;> field_simp <;> ring

theorem kernel_pos {l t : ℝ} (hl : 0 < l) (hl1 : l < 1)
    (ht : -1 < t) (ht1 : t < 1) (a b : Fin 2) : 0 < kernel l t a b := by
  have hp : 0 < pi t b := by fin_cases b <;> simp [pi] <;> linarith
  have hm : 0 < (1-l)*pi t b := mul_pos (by linarith) hp
  unfold kernel
  split_ifs <;> linarith

theorem stationary_pos {z : ℝ × ℝ} (hz : z ∈ interior) (a : Fin 2) :
    0 < stationary z a := by
  rcases hz with ⟨hu, hu1, hv, hv1⟩
  have hd : 0 < 2-z.1-z.2 := by linarith
  fin_cases a <;> simp [stationary] <;> exact div_pos (by linarith) hd

theorem trans_pos {z : ℝ × ℝ} (hz : z ∈ interior) (a b : Fin 2) :
    0 < trans z a b := by
  rcases hz with ⟨hu, hu1, hv, hv1⟩
  fin_cases a <;> fin_cases b <;> simp [trans] <;> linarith

theorem wordProb_pos {z : ℝ × ℝ} (hz : z ∈ interior) (n : ℕ)
    (w : Fin (n+1) → Fin 2) : 0 < wordProb z n w := by
  exact mul_pos (stationary_pos hz _) (Finset.prod_pos fun i _ => trans_pos hz _ _)

/-- The inverse chart is algebraic; the nonzero denominator is an explicit domain fact. -/
theorem inverse_chart {z : ℝ × ℝ} (hd : 2-z.1-z.2 ≠ 0) :
    chart (z.1+z.2-1) ((z.1-z.2)/(2-z.1-z.2)) = z := by
  apply Prod.ext <;> dsimp [chart] <;> field_simp <;> ring

#print axioms chart_trans
#print axioms pi_invariant
#print axioms steps_eq
#print axioms chart_mem_interior
#print axioms chart_stationary
#print axioms wordProb_pos
#print axioms inverse_chart
end
end MathDB333569
