import CoefficientBounds

open scoped BigOperators

namespace MaxIndex

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

def edgeDegree (i : α) (e : α × α) : ℝ :=
  (if e.1 = i then 1 else 0) + (if e.2 = i then 1 else 0)

def incidence (s : Finset (α × α)) (i : α) : ℝ :=
  (∑ e ∈ s, edgeDegree i e) / 2

def arithmeticEntry (p : α → ℝ) (e : α × α) : ℝ := (p e.1 + p e.2) / 2

def geometricEntry (p : α → ℝ) (e : α × α) : ℝ := Real.sqrt (p e.1 * p e.2)

theorem sum_arithmetic_eq_incidence (p : α → ℝ) (s : Finset (α × α)) :
    (∑ e ∈ s, arithmeticEntry p e) = ∑ i, incidence s i * p i := by
  simp only [arithmeticEntry, incidence]
  simp_rw [Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  simp only [edgeDegree, add_div, add_mul, Finset.sum_add_distrib, ite_div,
    one_div, zero_div, ite_mul, zero_mul]
  simp [eq_comm]
  ring

omit [Fintype α] in
theorem edgeDegree_le (i : α) (e : α × α) :
    edgeDegree i e ≤ 1 + if e = (i, i) then 1 else 0 := by
  rcases e with ⟨x, y⟩
  by_cases hx : x = i <;> by_cases hy : y = i <;> simp [edgeDegree, hx, hy]

omit [Fintype α] in
theorem incidence_le (s : Finset (α × α)) (i : α) :
    incidence s i ≤ ((s.card : ℝ) + 1) / 2 := by
  have hsum := Finset.sum_le_sum (s := s) (fun e _ => edgeDegree_le i e)
  have hone : (∑ e ∈ s, if e = (i, i) then (1 : ℝ) else 0) ≤ 1 := by
    simp only [Finset.sum_ite_eq']
    split_ifs <;> norm_num
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  dsimp [incidence]
  linarith

omit [Fintype α] in
theorem edgeDegree_pair_le (i j : α) (hij : i ≠ j) (e : α × α) :
    edgeDegree i e + edgeDegree j e ≤
      1 + if e ∈ ({i, j} : Finset α).product {i, j} then 1 else 0 := by
  rcases e with ⟨x, y⟩
  by_cases hxi : x = i <;> by_cases hxj : x = j <;>
    by_cases hyi : y = i <;> by_cases hyj : y = j <;>
    simp_all [edgeDegree]

omit [Fintype α] in
theorem incidence_pair_le (s : Finset (α × α)) (i j : α) (hij : i ≠ j) :
    incidence s i + incidence s j ≤ ((s.card : ℝ) + 4) / 2 := by
  let b := ({i, j} : Finset α).product {i, j}
  have hcard : b.card = 4 := by simp [b, hij]
  have hsub : s.filter (fun e => e ∈ b) ⊆ b := by
    intro e he
    exact (Finset.mem_filter.mp he).2
  have hcount : ((s.filter (fun e => e ∈ b)).card : ℝ) ≤ 4 := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq hcard
  have hone : (∑ e ∈ s, if e ∈ b then (1 : ℝ) else 0) ≤ 4 := by
    simpa only [Finset.sum_boole] using hcount
  have hsum := Finset.sum_le_sum (s := s) (fun e _ => edgeDegree_pair_le i j hij e)
  change (∑ e ∈ s, (edgeDegree i e + edgeDegree j e)) ≤
    (∑ e ∈ s, (1 + if e ∈ b then (1 : ℝ) else 0)) at hsum
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  dsimp [incidence]
  linarith

theorem arithmetic_low_maximum {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
    (p : α → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hsmall : ∀ i, p i ≤ 2 / 3) (m : ℕ) (s : Finset (α × α))
    (hs : s.card ≤ 2 * m + 1) :
    (∑ e ∈ s, arithmeticEntry p e) ≤ (4 * (m : ℝ) + 7) / 6 := by
  rw [sum_arithmetic_eq_incidence]
  apply weighted_coefficient_bound p (incidence s) m hp hsum hsmall
  · intro i
    have := incidence_le s i
    have hc : (s.card : ℝ) ≤ 2 * (m : ℝ) + 1 := by exact_mod_cast hs
    linarith
  · intro i j hij
    have := incidence_pair_le s i j hij
    have hc : (s.card : ℝ) ≤ 2 * (m : ℝ) + 1 := by exact_mod_cast hs
    linarith

end

end MaxIndex
