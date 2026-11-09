import BinaryDigits
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace JacobiShifted.BinaryFiltration

abbrev Exponent := Fin 2 →₀ ℕ
abbrev P (R : Type*) [CommRing R] := MvPolynomial (Fin 2) R

def weight (α : Exponent) : ℕ := sigma (α 0) + sigma (α 1) - 1

theorem sigma_coords_pos {α : Exponent} (hα : α ≠ 0) :
    1 ≤ sigma (α 0) + sigma (α 1) := by
  by_cases h0 : α 0 = 0
  · have h1 : α 1 ≠ 0 := by
      intro h1
      apply hα
      ext i
      fin_cases i <;> simp_all
    have := sigma_pos h1
    omega
  · have := sigma_pos h0
    omega

theorem weight_add_le {α β : Exponent} (hα : α ≠ 0) (hβ : β ≠ 0) :
    weight (α + β) ≤ weight α + weight β + 1 := by
  have ha := sigma_coords_pos hα
  have hb := sigma_coords_pos hβ
  have h0 := sigma_add_le (α 0) (β 0)
  have h1 := sigma_add_le (α 1) (β 1)
  simp only [weight, Finsupp.add_apply]
  omega

@[simp] theorem weight_double (α : Exponent) : weight (α + α) = weight α := by
  simp only [weight, Finsupp.add_apply, ← two_mul, sigma_double]

variable {R : Type*} [CommRing R]

/-- Genuine divisibility in the coefficient ring, with zero parameter constant term. -/
def Weighted (f : P R) : Prop :=
  f.coeff 0 = 0 ∧ ∀ α : Exponent, α ≠ 0 → (2 : R) ^ weight α ∣ f.coeff α

theorem weighted_zero : Weighted (0 : P R) := by
  constructor
  · simp
  · intro α _
    simp

theorem weighted_add {f g : P R} (hf : Weighted f) (hg : Weighted g) :
    Weighted (f + g) := by
  constructor
  · simp [hf.1, hg.1]
  · intro α hα
    simpa using dvd_add (hf.2 α hα) (hg.2 α hα)

theorem weighted_neg {f : P R} (hf : Weighted f) : Weighted (-f) := by
  constructor
  · simp [hf.1]
  · intro α hα
    simpa using dvd_neg.mpr (hf.2 α hα)

def weightedSubgroup : AddSubgroup (P R) where
  carrier := Weighted
  zero_mem' := weighted_zero
  add_mem' := weighted_add
  neg_mem' := weighted_neg

theorem weighted_sum {ι : Type*} (s : Finset ι) (f : ι → P R)
    (h : ∀ i ∈ s, Weighted (f i)) : Weighted (∑ i ∈ s, f i) :=
  (weightedSubgroup (R := R)).sum_mem h

theorem weighted_monomial {α : Exponent} {c : R} (hα : α ≠ 0)
    (hc : (2 : R) ^ weight α ∣ c) : Weighted (MvPolynomial.monomial α c) := by
  classical
  constructor
  · simp [MvPolynomial.coeff_monomial, hα]
  · intro β _
    by_cases hb : α = β
    · simpa [MvPolynomial.coeff_monomial, hb] using hc
    · simp [MvPolynomial.coeff_monomial, hb]

theorem support_nonzero {f : P R} (hf : Weighted f) {α : Exponent}
    (hα : α ∈ f.support) : α ≠ 0 := by
  intro he
  subst α
  exact (MvPolynomial.mem_support_iff.mp hα) hf.1

theorem weighted_support_monomial {f : P R} (hf : Weighted f) {α : Exponent}
    (hα : α ∈ f.support) : Weighted (MvPolynomial.monomial α (f.coeff α)) :=
  weighted_monomial (support_nonzero hf hα) (hf.2 α (support_nonzero hf hα))

theorem double_monomial_product {α β : Exponent} {c d : R}
    (hα : α ≠ 0) (hβ : β ≠ 0)
    (hc : (2 : R) ^ weight α ∣ c) (hd : (2 : R) ^ weight β ∣ d) :
    Weighted (2 * MvPolynomial.monomial α c * MvPolynomial.monomial β d) := by
  have hab : α + β ≠ 0 := by
    intro he
    have : α = 0 := (add_eq_zero.mp he).1
    exact hα this
  have hdiv : (2 : R) ^ weight (α + β) ∣ 2 * c * d := by
    apply dvd_trans (pow_dvd_pow (2 : R) (weight_add_le hα hβ))
    obtain ⟨x, rfl⟩ := hc
    obtain ⟨y, rfl⟩ := hd
    refine ⟨x * y, ?_⟩
    simp only [pow_add, pow_one]
    ring
  have hm : (2 : P R) * MvPolynomial.monomial α c * MvPolynomial.monomial β d =
      MvPolynomial.monomial (α + β) (2 * c * d) := by
    rw [show (2 : P R) = MvPolynomial.monomial 0 (2 : R) by rfl,
      MvPolynomial.monomial_mul_monomial, MvPolynomial.monomial_mul_monomial, zero_add]
  rw [hm]
  exact weighted_monomial hab hdiv

/-- Expansion into actual polynomial monomials proves the off-diagonal factor-two closure. -/
theorem weighted_two_mul {f g : P R} (hf : Weighted f) (hg : Weighted g) :
    Weighted (2 * f * g) := by
  classical
  conv => arg 1; rw [f.as_sum, g.as_sum]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply weighted_sum
  intro β hβ
  apply weighted_sum
  intro α hα
  exact double_monomial_product (support_nonzero hf hα) (support_nonzero hg hβ)
    (hf.2 α (support_nonzero hf hα)) (hg.2 β (support_nonzero hg hβ))

theorem weighted_monomial_square {α : Exponent} {c : R} (hα : α ≠ 0)
    (hc : (2 : R) ^ weight α ∣ c) :
    Weighted ((MvPolynomial.monomial α c : P R) ^ 2) := by
  rw [pow_two, MvPolynomial.monomial_mul_monomial]
  apply weighted_monomial
  · intro he
    exact hα (add_eq_zero.mp he).1
  · rw [weight_double]
    -- Diagonal parameter terms use 2q ≥ q, with q(2α) = q(α).
    apply dvd_trans (pow_dvd_pow (2 : R) (Nat.le_add_right (weight α) (weight α)))
    simpa only [pow_add] using mul_dvd_mul hc hc

/-- The identity explicitly pairs the two unequal parameter blocks. -/
theorem square_add_identity (f g : P R) :
    (f + g) ^ 2 = f ^ 2 + g ^ 2 + 2 * f * g := by ring

/-- Finite monomial expansion: diagonal squares and paired unequal monomials. -/
theorem weighted_sum_square {ι : Type*} (s : Finset ι) (f : ι → P R)
    (hf : ∀ i ∈ s, Weighted (f i)) (hsq : ∀ i ∈ s, Weighted ((f i) ^ 2)) :
    Weighted ((∑ i ∈ s, f i) ^ 2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (weighted_zero (R := R))
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, square_add_identity]
    exact weighted_add (weighted_add (hsq a (by simp))
      (ih (fun i hi => hf i (by simp [hi])) (fun i hi => hsq i (by simp [hi]))))
      (weighted_two_mul (hf a (by simp))
        (weighted_sum s f (fun i hi => hf i (by simp [hi]))))

theorem weighted_square {f : P R} (hf : Weighted f) : Weighted (f ^ 2) := by
  classical
  conv => arg 1; rw [f.as_sum]
  exact weighted_sum_square f.support (fun α => MvPolynomial.monomial α (f.coeff α))
    (fun _ hα => weighted_support_monomial hf hα)
    (fun α hα => weighted_monomial_square (support_nonzero hf hα)
      (hf.2 α (support_nonzero hf hα)))

/-- Coefficientwise extension of a genuine additive coefficient map. -/
def coefficientOperator (δ : R →+ R) : P R →+ P R where
  toFun f := AddMonoidAlgebra.map δ f
  map_zero' := by ext α; simp
  map_add' f g := by ext α; simp

@[simp] theorem coefficientOperator_coeff (δ : R →+ R) (f : P R) (α : Exponent) :
    (coefficientOperator δ f).coeff α = δ (f.coeff α) := rfl

theorem additive_nat_mul (δ : R →+ R) (m : ℕ) (x : R) :
    δ ((m : R) * x) = (m : R) * δ x := by
  simpa only [nsmul_eq_mul] using δ.map_nsmul m x

theorem weighted_coefficientOperator (δ : R →+ R) {f : P R} (hf : Weighted f) :
    Weighted (coefficientOperator δ f) := by
  constructor
  · simp [hf.1]
  · intro α hα
    obtain ⟨x, hx⟩ := hf.2 α hα
    refine ⟨δ x, ?_⟩
    rw [coefficientOperator_coeff, hx]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using additive_nat_mul δ (2 ^ weight α) x

end JacobiShifted.BinaryFiltration
