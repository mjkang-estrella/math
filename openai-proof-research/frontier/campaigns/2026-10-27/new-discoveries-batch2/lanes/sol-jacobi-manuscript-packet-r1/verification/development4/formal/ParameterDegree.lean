import MidpointSequence
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.CommRing

set_option autoImplicit false
set_option warningAsError true

noncomputable section
namespace JacobiShifted.ParameterDegree
open MvPolynomial
open JacobiShifted.BinaryFiltration

variable {S : Type*} [CommRing S]

/-- Coefficient differentiation cannot create a parameter monomial. -/
theorem coefficientOperator_totalDegree (D : S →+ S) (f : P S) :
    (coefficientOperator D f).totalDegree ≤ f.totalDegree := by
  apply totalDegree_le_of_support_subset
  intro a ha
  rw [mem_support_iff, coefficientOperator_coeff] at ha
  rw [mem_support_iff]
  intro he
  exact ha (by rw [he, map_zero])

theorem initial_totalDegree (a b : S) : (initial a b).totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · exact (totalDegree_monomial_le _ _).trans (by simp)
  · exact (totalDegree_monomial_le _ _).trans (by simp)

/-- A bound for every index of the concrete integral recurrence, including zero. -/
theorem h_totalDegree (n : ℕ) : (Midpoint.h n).totalDegree ≤ (n+1)/2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      by_cases hn : n=0
      · subst n
        simpa [Midpoint.P] using initial_totalDegree (Midpoint.w^2) (Midpoint.w*Midpoint.x)
      rw [Midpoint.h_recurrence n (by omega)]
      apply (totalDegree_sub _ _).trans
      apply max_le
      · rw [totalDegree_neg]
        exact (coefficientOperator_totalDegree _ _).trans ((ih n (by omega)).trans (by omega))
      · apply totalDegree_finsetSum_le
        intro i hi
        have hi' : i≤n := by simpa using hi
        have ha := ih i (by omega)
        have hb := ih (n-i) (by omega)
        apply (totalDegree_mul _ _).trans
        omega

/-- Every exponent above the integral parameter-degree bound has zero coefficient. -/
theorem h_coeff_eq_zero (n : ℕ) (a : Exponent)
    (ha : (n+1)/2 < a.degree) : (Midpoint.h n).coeff a=0 := by
  apply coeff_eq_zero_of_totalDegree_lt
  exact lt_of_le_of_lt (h_totalDegree n) ha

theorem exponent_degree (a : Exponent) : a.degree=a 0+a 1 := by
  change a.sum (fun _ n => n)=_
  rw [Finsupp.sum_fintype]
  · simp [Fin.sum_univ_two]
  · intro i; rfl

/-- Requested bidegree version on the actual integral `h`. -/
theorem h_bidegree_eq_zero (n i j : ℕ) (hij : (n+1)/2 < i+j) :
    (Midpoint.h n).coeff (bidegree i j)=0 := by
  apply h_coeff_eq_zero
  simpa [exponent_degree] using hij

/-- Multiplication at the largest allowed degree only sees the two top layers. -/
theorem top_mul (f g : P S) (a b : ℕ)
    (hf : f.totalDegree≤a) (hg : g.totalDegree≤b) :
    homogeneousComponent (a+b) (f*g)=
      homogeneousComponent a f*homogeneousComponent b g := by
  classical
  ext c
  rw [coeff_homogeneousComponent]
  simp only [coeff_mul, coeff_homogeneousComponent]
  by_cases hc : c.degree=a+b
  · rw [ite_eq_left hc]
    apply Finset.sum_congr rfl
    intro xy hxy
    have he := Finset.mem_antidiagonal.mp hxy
    by_cases hx : f.coeff xy.1=0
    · simp [hx]
    by_cases hy : g.coeff xy.2=0
    · simp [hy]
    have hx' : xy.1.degree≤a := (le_totalDegree (mem_support_iff.mpr hx)).trans hf
    have hy' : xy.2.degree≤b := (le_totalDegree (mem_support_iff.mpr hy)).trans hg
    have hs : xy.1.degree+xy.2.degree=a+b := by rw [← map_add, he, hc]
    have hxa : xy.1.degree=a := by omega
    have hyb : xy.2.degree=b := by omega
    simp [hxa,hyb]
  · rw [ite_eq_right hc]
    symm
    apply Finset.sum_eq_zero
    intro xy hxy
    have he := Finset.mem_antidiagonal.mp hxy
    by_cases hxa : xy.1.degree=a
    · by_cases hyb : xy.2.degree=b
      · exact False.elim (hc (by rw [← he,map_add,hxa,hyb]))
      · simp [hyb]
    · simp [hxa]

end JacobiShifted.ParameterDegree
