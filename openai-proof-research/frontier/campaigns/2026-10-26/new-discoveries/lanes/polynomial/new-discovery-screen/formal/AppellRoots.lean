import MomentPolynomials

noncomputable section
open Finset Polynomial
namespace OddRootMeans

def appell (a : ℕ → ℂ) (m : ℕ) : ℂ[X] :=
  ∑ j ∈ range (m+1), monomial j ((m.choose j : ℂ) * a (m-j))

lemma appell_coeff (a : ℕ → ℂ) (m j : ℕ) :
    (appell a m).coeff j = (m.choose j : ℂ) * a (m-j) := by
  classical
  simp only [appell, finsetSum_coeff, coeff_monomial]
  by_cases hj : j < m+1
  · simp [hj]
  · simp [hj, Nat.choose_eq_zero_of_lt (show m < j by omega)]

lemma appell_degree_le (a : ℕ → ℂ) (m : ℕ) : (appell a m).natDegree ≤ m := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  simp [appell_coeff, Nat.choose_eq_zero_of_lt hj]

lemma appell_degree (a : ℕ → ℂ) (ha : a 0 = 1) (m : ℕ) :
    (appell a m).natDegree = m := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (appell_degree_le a m)
  simp [appell_coeff, ha]

lemma appell_monic (a : ℕ → ℂ) (ha : a 0 = 1) (m : ℕ) : (appell a m).Monic := by
  rw [Monic, leadingCoeff, appell_degree a ha m]
  simp [appell_coeff, ha]

lemma appell_reverse_coeff (a : ℕ → ℂ) (m i : ℕ) (hi : i≤m) :
    (appell a m).coeff (m-i) = (m.choose i : ℂ) * a i := by
  rw [appell_coeff, Nat.choose_symm hi, Nat.sub_sub_self hi]

lemma appell_derivative (a : ℕ → ℂ) (m : ℕ) :
    (appell a (m+1)).derivative = C (m+1 : ℂ) * appell a m := by
  ext j
  simp only [coeff_derivative, appell_coeff, coeff_C_mul]
  have h := congrArg (Nat.cast : ℕ → ℂ) (Nat.add_one_mul_choose_eq m j)
  push_cast at h
  rw [show m+1-(j+1)=m-j by omega]
  linear_combination -a (m-j) * h

lemma appell_roots_moment (a : ℕ → ℂ) (ha : a 0 = 1) (m i : ℕ) :
    (m : ℂ) * (normMoment a i).eval (m : ℂ) = powerSum (appell a m).roots i := by
  exact normMoment_eval_roots _ (appell_monic a ha m) m (appell_degree a ha m)
    a (appell_reverse_coeff a m) i

lemma appell_iterated_derivative (a : ℕ → ℂ) (D r : ℕ) (hr : r≤D) :
    derivative^[r] (appell a D) = C (D.descFactorial r : ℂ) * appell a (D-r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih (by omega), derivative_C_mul]
    have hD : D-r = (D-(r+1))+1 := by omega
    rw [hD, appell_derivative, Nat.descFactorial_succ, Nat.cast_mul,
      ← mul_assoc, ← C_mul]
    congr 1
    rw [hD]
    congr 1
    push_cast
    ring

lemma appell_derivative_roots (a : ℕ → ℂ) (D m : ℕ) (hm : m≤D) :
    (derivative^[D-m] (appell a D)).roots = (appell a m).roots := by
  rw [appell_iterated_derivative a D (D-m) (Nat.sub_le ..), Nat.sub_sub_self hm,
    roots_C_mul]
  exact Nat.cast_ne_zero.mpr (Nat.descFactorial_pos.mpr (Nat.sub_le ..)).ne'

lemma appell_eval (a : ℕ → ℂ) (D : ℕ) (z : ℂ) :
    (appell a D).eval z = ∑ j ∈ range (D+1), (D.choose j : ℂ) * a (D-j) * z^j := by
  simp [appell, eval_finsetSum]

lemma appell_sum_eval (a : ℕ → ℂ) (D : ℕ) (s : Multiset ℂ) :
    (s.map (fun z => (appell a D).eval z)).sum =
      ∑ j ∈ range (D+1), (D.choose j : ℂ) * a (D-j) * powerSum s j := by
  induction s using Multiset.induction_on with
  | empty => simp [powerSum]
  | cons z s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, appell_eval]
    simp [powerSum, mul_add, sum_add_distrib]

end OddRootMeans
