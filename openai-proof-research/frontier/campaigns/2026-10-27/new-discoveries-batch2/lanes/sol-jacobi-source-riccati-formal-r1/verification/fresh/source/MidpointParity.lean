import MidpointSequence

set_option autoImplicit false
set_option warningAsError true
set_option linter.unnecessarySeqFocus false

noncomputable section
namespace JacobiShifted.Midpoint
open JacobiShifted.BinaryFiltration

/-- Additive maps preserve the integral signs used by both parity gradings. -/
theorem additive_sign (δ : R →+ R) (k : ℕ) (z : R) :
    δ ((-1 : R)^k*z) = (-1 : R)^k*δ z := by
  induction k with
  | zero => simp
  | succ k ih => simpa [pow_succ, neg_mul, mul_neg] using congrArg Neg.neg ih

def RhoParity (f : Param) : Prop :=
  ∀ α : Exponent, rho (f.coeff α) = (-1 : R)^(α 1)*f.coeff α

theorem rhoParity_zero : RhoParity 0 := by intro α; simp

theorem rhoParity_add {f g : Param} (hf : RhoParity f) (hg : RhoParity g) :
    RhoParity (f+g) := by
  intro α
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add, hf α, hg α]
  ring

theorem rhoParity_neg {f : Param} (hf : RhoParity f) : RhoParity (-f) := by
  intro α
  simp [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, hf α]

theorem rhoParity_sum {ι : Type*} (s : Finset ι) (f : ι → Param)
    (hf : ∀ i ∈ s, RhoParity (f i)) : RhoParity (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rhoParity_zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact rhoParity_add (hf a (by simp)) (ih (fun i hi => hf i (by simp [hi])))

theorem rhoParity_mul {f g : Param} (hf : RhoParity f) (hg : RhoParity g) :
    RhoParity (f*g) := by
  classical
  intro γ
  rw [coefficient_product_expansion]
  simp only [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  by_cases he : α+β=γ
  · subst γ
    simp only [ite_true, map_mul, hf α, hg β, Finsupp.add_apply, pow_add]
    ring
  · simp [he]

theorem rhoParity_delta {f : Param} (hf : RhoParity f) :
    RhoParity (coefficientOperator delta f) := by
  intro α
  simp only [coefficientOperator_coeff, rho_partial, hf α, additive_sign]

theorem rhoParity_monomial (α : Exponent) (z : R)
    (hz : rho z = (-1 : R)^(α 1)*z) : RhoParity (MvPolynomial.monomial α z) := by
  classical
  intro β
  by_cases he : α=β
  · subst β
    simpa using hz
  · simp [MvPolynomial.coeff_monomial, he]

theorem rhoParity_P : RhoParity P := by
  apply rhoParity_add
  · apply rhoParity_monomial
    simp [map_pow]
  · apply rhoParity_monomial
    simp [map_mul]

theorem h_rhoParity (n : ℕ) : RhoParity (h n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · simpa using rhoParity_zero
    · by_cases hn : n=0
      · simpa [hn] using rhoParity_P
      · rw [h_recurrence n (by omega), sub_eq_add_neg]
        apply rhoParity_add (rhoParity_neg (rhoParity_delta (ih n (by omega))))
        apply rhoParity_neg
        apply rhoParity_sum
        intro i hi
        have hi' := Finset.mem_range.mp hi
        exact rhoParity_mul (ih i (by omega)) (ih (n-i) (by omega))

/-- The independent spectral-index parity under `(x,w) ↦ (-x,-w)`. -/
def TauParity (k : ℕ) (f : Param) : Prop :=
  ∀ α : Exponent, tau (f.coeff α) = (-1 : R)^k*f.coeff α

theorem tauParity_zero (k : ℕ) : TauParity k 0 := by intro α; simp

theorem tauParity_add {k : ℕ} {f g : Param} (hf : TauParity k f) (hg : TauParity k g) :
    TauParity k (f+g) := by
  intro α
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add, hf α, hg α]
  ring

theorem tauParity_neg {k : ℕ} {f : Param} (hf : TauParity k f) : TauParity k (-f) := by
  intro α
  simp [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, hf α]

theorem tauParity_sum {ι : Type*} {k : ℕ} (s : Finset ι) (f : ι → Param)
    (hf : ∀ i ∈ s, TauParity k (f i)) : TauParity k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tauParity_zero k
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact tauParity_add (hf a (by simp)) (ih (fun i hi => hf i (by simp [hi])))

theorem tauParity_mul {k l : ℕ} {f g : Param}
    (hf : TauParity k f) (hg : TauParity l g) : TauParity (k+l) (f*g) := by
  classical
  intro γ
  rw [coefficient_product_expansion]
  simp only [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  by_cases he : α+β=γ
  · simp only [ite_eq_left he, map_mul, hf α, hg β, pow_add]
    ring
  · simp [he]

theorem tauParity_delta {k : ℕ} {f : Param} (hf : TauParity k f) :
    TauParity (k+1) (coefficientOperator delta f) := by
  intro α
  simp only [coefficientOperator_coeff, tau_partial, hf α, additive_sign]
  simp [pow_succ, mul_neg]

theorem tauParity_monomial (k : ℕ) (α : Exponent) (z : R)
    (hz : tau z = (-1 : R)^k*z) : TauParity k (MvPolynomial.monomial α z) := by
  classical
  intro β
  by_cases he : α=β
  · subst β
    simpa using hz
  · simp [MvPolynomial.coeff_monomial, he]

theorem tauParity_P : TauParity 2 P := by
  apply tauParity_add
  · apply tauParity_monomial
    simp [map_pow]
  · apply tauParity_monomial
    simp [map_mul]

theorem h_tauParity (n : ℕ) : TauParity (n+1) (h n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · simpa using tauParity_zero 1
    · by_cases hn : n=0
      · simpa [hn] using tauParity_P
      · rw [h_recurrence n (by omega), sub_eq_add_neg]
        apply tauParity_add (tauParity_neg (tauParity_delta (ih n (by omega))))
        apply tauParity_neg
        apply tauParity_sum
        intro i hi
        have hi' := Finset.mem_range.mp hi
        have hp := tauParity_mul (ih i (by omega)) (ih (n-i) (by omega))
        convert hp using 1 <;> omega

/-- Every actual parameter coefficient is in the integral principal ideal `(w)`. -/
def WCoefficients (f : Param) : Prop := ∀ α : Exponent, InW (f.coeff α)

theorem inW_sum {ι : Type*} (s : Finset ι) (f : ι → R)
    (hf : ∀ i ∈ s, InW (f i)) : InW (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using inW_zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact inW_add (hf a (by simp)) (ih (fun i hi => hf i (by simp [hi])))

theorem wCoefficients_zero : WCoefficients 0 := by intro α; simpa using inW_zero

theorem wCoefficients_add {f g : Param} (hf : WCoefficients f) (hg : WCoefficients g) :
    WCoefficients (f+g) := by
  intro α
  simpa using inW_add (hf α) (hg α)

theorem wCoefficients_neg {f : Param} (hf : WCoefficients f) : WCoefficients (-f) := by
  intro α
  simpa using inW_neg (hf α)

theorem wCoefficients_sum {ι : Type*} (s : Finset ι) (f : ι → Param)
    (hf : ∀ i ∈ s, WCoefficients (f i)) : WCoefficients (∑ i ∈ s, f i) := by
  intro α
  rw [MvPolynomial.coeff_sum]
  exact inW_sum s _ (fun i hi => hf i hi α)

theorem wCoefficients_mul {f g : Param} (hf : WCoefficients f) : WCoefficients (f*g) := by
  classical
  intro γ
  rw [coefficient_product_expansion]
  apply inW_sum
  intro α _
  apply inW_sum
  intro β _
  split_ifs
  · exact inW_mul_right (hf α) _
  · exact inW_zero

theorem wCoefficients_delta {f : Param} (hf : WCoefficients f) :
    WCoefficients (coefficientOperator delta f) := by
  intro α
  exact inW_partial (hf α)

theorem wCoefficients_monomial (α : Exponent) (z : R) (hz : InW z) :
    WCoefficients (MvPolynomial.monomial α z) := by
  classical
  intro β
  by_cases he : α=β
  · subst β
    simpa using hz
  · simpa [MvPolynomial.coeff_monomial, he] using inW_zero

theorem wCoefficients_P : WCoefficients P := by
  apply wCoefficients_add
  · apply wCoefficients_monomial
    exact ⟨w, by rw [pow_two]⟩
  · apply wCoefficients_monomial
    exact ⟨x,rfl⟩

theorem h_wCoefficients (n : ℕ) : WCoefficients (h n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · simpa using wCoefficients_zero
    · by_cases hn : n=0
      · simpa [hn] using wCoefficients_P
      · rw [h_recurrence n (by omega), sub_eq_add_neg]
        apply wCoefficients_add (wCoefficients_neg (wCoefficients_delta (ih n (by omega))))
        apply wCoefficients_neg
        apply wCoefficients_sum
        intro i hi
        have hi' := Finset.mem_range.mp hi
        exact wCoefficients_mul (ih i (by omega))

theorem h_coefficient_re_divisible (n : ℕ) (α : Exponent) : q ∣ ((h n).coeff α).re :=
  (inW_iff _).mp (h_wCoefficients n α)

theorem h_rho_coefficient (n i j : ℕ) :
    rho ((h n).coeff (bidegree i j)) = (-1 : R)^j*(h n).coeff (bidegree i j) := by
  simpa using h_rhoParity n (bidegree i j)

theorem h_tau_coefficient (n : ℕ) (α : Exponent) :
    tau ((h n).coeff α) = (-1 : R)^(n+1)*(h n).coeff α := h_tauParity n α

theorem h_coefficient_mem_w (n : ℕ) (α : Exponent) :
    (h n).coeff α ∈ Ideal.span ({w} : Set R) :=
  (inW_ideal_span _).mp (h_wCoefficients n α)

end JacobiShifted.Midpoint
