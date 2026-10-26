import MeanPolynomial

noncomputable section
open Finset Polynomial
namespace OddRootMeans

lemma finite_difference_sum (P : ℂ[X]) (D : ℕ) (h : P.natDegree<D) :
    (∑ m ∈ range (D+1), (-1 : ℂ)^(D-m) * (D.choose m : ℂ) * P.eval (m:ℂ)) = 0 := by
  have hfd := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt h) 0
  rw [fwdDiff_iter_eq_sum_shift] at hfd
  simpa only [Pi.zero_apply, zero_add, nsmul_eq_mul, mul_one, zsmul_eq_mul,
    Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast] using hfd

lemma finite_difference_reflected_sum (P : ℂ[X]) (D : ℕ) (h : P.natDegree<D) :
    (∑ r ∈ range (D+1), (-1 : ℂ)^r * (D.choose r : ℂ) * P.eval ((D-r:ℕ):ℂ)) = 0 := by
  have hf := finite_difference_sum P D h
  rw [← sum_range_reflect] at hf
  simp only [Nat.add_sub_cancel] at hf
  rw [← hf]
  apply sum_congr rfl
  intro r hr
  have hr' : r≤D := by have := mem_range.mp hr; omega
  rw [Nat.sub_sub_self hr', Nat.choose_symm hr']

/-- Source mean: repeated roots occur repeatedly in the roots multiset. -/
def derivativeRootMean (p : ℂ[X]) (r : ℕ) : ℂ :=
  ((derivative^[r] p).roots.map (fun z => p.eval z)).sum / (p.natDegree-r : ℕ)

lemma appell_derivativeRootMean (a : ℕ → ℂ) (ha : a 0 = 1) (D r : ℕ) (hr : r<D) :
    derivativeRootMean (appell a D) r = (meanPolynomial a D).eval ((D-r:ℕ):ℂ) := by
  have hr' : r≤D := by omega
  have hroots : (derivative^[r] (appell a D)).roots = (appell a (D-r)).roots := by
    simpa only [Nat.sub_sub_self hr'] using
      appell_derivative_roots a D (D-r) (Nat.sub_le ..)
  rw [derivativeRootMean, appell_degree a ha D, hroots]
  apply (div_eq_iff (Nat.cast_ne_zero.mpr (show D-r ≠ 0 by omega))).mpr
  simpa only [mul_comm] using (meanPolynomial_roots a ha D (D-r)).symm

lemma appell_odd_identity (a : ℕ → ℂ) (ha : a 0 = 1) (D : ℕ) (hD : Odd D) :
    (∑ r ∈ Ioo 0 D, (-1 : ℂ)^r * (D.choose r : ℂ) *
      derivativeRootMean (appell a D) r) = 0 := by
  have hDpos : 0<D := hD.pos
  have hdeg : (meanPolynomial a D).natDegree<D :=
    (meanPolynomial_degree a D).trans_lt (by omega)
  have hf := finite_difference_reflected_sum (meanPolynomial a D) D hdeg
  have hsub : Ioo 0 D ⊆ range (D+1) := by
    intro r hr
    simp only [mem_Ioo, mem_range] at *
    omega
  have heq : (∑ r ∈ Ioo 0 D, (-1 : ℂ)^r * (D.choose r : ℂ) *
      (meanPolynomial a D).eval ((D-r:ℕ):ℂ)) =
      ∑ r ∈ range (D+1), (-1 : ℂ)^r * (D.choose r : ℂ) *
      (meanPolynomial a D).eval ((D-r:ℕ):ℂ) := by
    apply sum_subset hsub
    intro r hr hnot
    have hr' : r=0 ∨ r=D := by
      simp only [mem_range] at hr
      simp only [mem_Ioo, not_and_or, not_lt] at hnot
      omega
    rcases hr' with hzero | hlast
    · subst r
      simp [meanPolynomial_at_degree a ha D hDpos]
    · subst r
      simp [meanPolynomial_zero a ha D hD]
  rw [← heq] at hf
  convert hf using 1
  apply sum_congr rfl
  intro r hr
  rw [appell_derivativeRootMean a ha D r (mem_Ioo.mp hr).2]

end OddRootMeans
