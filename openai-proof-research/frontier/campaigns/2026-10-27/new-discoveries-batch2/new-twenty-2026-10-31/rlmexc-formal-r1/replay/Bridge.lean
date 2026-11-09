import Definitions
namespace AK350721
open scoped Classical
open Finset MvPolynomial
noncomputable def degreeSet {n : ℕ} (R E : Finset (Fin n)) : (Fin n ⊕ Fin n) →₀ ℕ :=
  (∑ i ∈ R, Finsupp.single (Sum.inl i) 1) + ∑ i ∈ E, Finsupp.single (Sum.inr i) 1

theorem degreeSet_inl {n : ℕ} (R E : Finset (Fin n)) (i : Fin n) :
    degreeSet R E (Sum.inl i) = if i ∈ R then 1 else 0 := by
  classical
  simp [degreeSet, Finsupp.single_apply, Finset.sum_ite_eq', Sum.inl_injective.eq_iff]

theorem degreeSet_inr {n : ℕ} (R E : Finset (Fin n)) (i : Fin n) :
    degreeSet R E (Sum.inr i) = if i ∈ E then 1 else 0 := by
  classical
  simp [degreeSet, Finsupp.single_apply, Finset.sum_ite_eq', Sum.inr_injective.eq_iff]

theorem degreeSet_injective {n : ℕ} (R E R' E' : Finset (Fin n)) :
    degreeSet R E = degreeSet R' E' ↔ R = R' ∧ E = E' := by
  classical
  constructor
  · intro h
    constructor
    · ext i
      have := congrArg (fun m => m (Sum.inl i)) h
      simp only [degreeSet_inl] at this
      split_ifs at this <;> simp_all
    · ext i
      have := congrArg (fun m => m (Sum.inr i)) h
      simp only [degreeSet_inr] at this
      split_ifs at this <;> simp_all
  · rintro ⟨rfl, rfl⟩; rfl

theorem term_eq_monomial {n : ℕ} (pi : Equiv.Perm (Fin n)) :
    term pi = monomial (degreeSet (rlmv pi) (excv pi)) 1 := by
  classical
  unfold term degreeSet
  rw [show (1 : ℤ) = 1 * 1 from rfl, ← monomial_mul_monomial]
  congr 1
  · simpa [X] using (monomial_sum_prod (rlmv pi)
      (fun i => Finsupp.single (Sum.inl i) 1) (fun _ => (1 : ℤ))).symm
  · simpa [X] using (monomial_sum_prod (excv pi)
      (fun i => Finsupp.single (Sum.inr i) 1) (fun _ => (1 : ℤ))).symm

theorem coeff_rawSum {n k : ℕ} (R E : Finset (Fin n)) :
    (rawSum n k).coeff (degreeSet R E) =
      ∑ pi ∈ univ.filter (fun pi : Equiv.Perm (Fin n) =>
        cycleGe k pi ∧ rlmv pi = R ∧ excv pi = E), (-1 : ℤ) ^ invCount pi := by
  classical
  simp only [rawSum, coeff_sum, coeff_C_mul, term_eq_monomial, coeff_monomial]
  simp only [degreeSet_injective]
  simp [Finset.sum_filter, eq_comm, ite_and, mul_ite]
end AK350721
