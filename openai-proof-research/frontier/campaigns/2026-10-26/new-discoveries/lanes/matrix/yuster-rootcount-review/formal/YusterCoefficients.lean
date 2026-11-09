import Mathlib

namespace YusterCounterexample

/-- Integral dynamic rows: these equal (k-1)! times the source C(k,t,j). -/
def coeffRow (k : ℕ) : ℕ → List ℤ
  | 0 => [1]
  | t+1 => (List.range (t+2)).map fun j => if j=0 then 0 else
      ((k:ℤ)*j-t)*(coeffRow k t).getD j 0 + (k:ℤ)*(coeffRow k t).getD (j-1) 0

lemma coeffRow_length (k t : ℕ) : (coeffRow k t).length=t+1 := by
  cases t <;> simp [coeffRow]

lemma coeffRow_zero (k t : ℕ) : (coeffRow k (t+1)).getD 0 0=0 := by
  simp [coeffRow]

lemma coeffRow_recurrence (k t j : ℕ) (hj : 0<j) :
    (coeffRow k (t+1)).getD j 0 =
      ((k:ℤ)*j-t)*(coeffRow k t).getD j 0 + (k:ℤ)*(coeffRow k t).getD (j-1) 0 := by
  by_cases h : j<t+2
  · simp [coeffRow, List.getD_eq_getElem?_getD,
      h, Nat.ne_of_gt hj]
  · have hjt : t+1≤j := by omega
    have hjt' : t+1≤j-1 := by omega
    have h1 : (coeffRow k t).getD j 0 = 0 :=
      List.getD_eq_default _ _ (by rw [coeffRow_length]; omega)
    have h2 : (coeffRow k t).getD (j-1) 0 = 0 :=
      List.getD_eq_default _ _ (by rw [coeffRow_length]; omega)
    rw [h1, h2]
    simp [coeffRow_length, h]

/-- Exact rational coefficients in Yuster Lemma3.5 and Corollary3.7. -/
def sourceC (k t j : ℕ) : ℚ := ((coeffRow k t).getD j 0 : ℚ) / (k-1).factorial

lemma sourceC_initial (k : ℕ) : sourceC k 0 0 = 1 / ((k-1).factorial : ℚ) := by
  simp [sourceC, coeffRow]

lemma sourceC_zero_row (k j : ℕ) (hj : 0<j) : sourceC k 0 j = 0 := by
  cases j with
  | zero => omega
  | succ j => simp [sourceC, coeffRow]

lemma sourceC_zero_column (k t : ℕ) : sourceC k (t+1) 0 = 0 := by
  unfold sourceC
  rw [coeffRow_zero]
  norm_num

lemma sourceC_recurrence (k t j : ℕ) (hj : 0<j) :
    sourceC k (t+1) j = ((k:ℚ)*j-t) * sourceC k t j +
      (k:ℚ) * sourceC k t (j-1) := by
  simp only [sourceC, coeffRow_recurrence k t j hj]
  push_cast
  ring

end YusterCounterexample
