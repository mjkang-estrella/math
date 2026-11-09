import UlasFinal2
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Positivity

set_option linter.unusedSimpArgs false
open Polynomial
namespace Ulas.Round3
/-- Divisibility version of the bit-length weight, valid also at zero coefficients. -/
def Weighted (v : ℕ) (R : Polynomial ℤ) : Prop :=
  ∀ E, (2 : ℤ)^(v + E.size) ∣ R.coeff E

theorem size_le_self (n : ℕ) : n.size ≤ n := by
  apply Nat.size_le.mpr
  exact Nat.lt_two_pow_self

theorem size_double (e : ℕ) (he : e ≠ 0) : (2*e).size = e.size+1 := by
  simpa [Nat.bit, two_mul] using (Nat.size_bit (b := false) (n := e) (by simpa [Nat.bit] using he))

theorem size_double_add_one (e : ℕ) : (2*e+1).size = e.size+1 := by
  simpa [Nat.bit, two_mul, Nat.succ_eq_add_one] using
    (Nat.size_bit (b := true) (n := e) (by simp [Nat.bit]))

theorem size_add_le (e i : ℕ) : (e+i).size ≤ e.size+i.size := by
  by_cases he : e = 0
  · simp [he]
  by_cases hi : i = 0
  · simp [hi]
  have he' := Nat.size_pos.mpr (Nat.pos_of_ne_zero he)
  have hi' := Nat.size_pos.mpr (Nat.pos_of_ne_zero hi)
  apply Nat.size_le.mpr
  rw [pow_add]
  have ha := Nat.lt_size_self e
  have hb := Nat.lt_size_self i
  have h2a : 2 ≤ 2^e.size := Nat.pow_le_pow_right (by decide : 0 < 2) he'
  have h2b : 2 ≤ 2^i.size := Nat.pow_le_pow_right (by decide : 0 < 2) hi'
  nlinarith

theorem weighted_zero (v : ℕ) : Weighted v 0 := by intro E; simp

theorem weighted_add {v : ℕ} {R S : Polynomial ℤ}
    (hR : Weighted v R) (hS : Weighted v S) : Weighted v (R+S) := by
  intro E
  simpa using dvd_add (hR E) (hS E)

theorem weighted_sum {α : Type*} (s : Finset α) (f : α → Polynomial ℤ) (v : ℕ)
    (h : ∀ a ∈ s, Weighted v (f a)) : Weighted v (∑ a ∈ s, f a) := by
  intro E
  simpa only [finsetSum_coeff] using Finset.dvd_sum (fun a ha => h a ha E)

theorem weighted_mono {v w : ℕ} {R : Polynomial ℤ} (h : Weighted w R)
    (hv : v ≤ w) : Weighted v R := by
  intro E
  exact dvd_trans (pow_dvd_pow _ (by omega)) (h E)

theorem weighted_monomial (v E : ℕ) (a : ℤ)
    (h : (2 : ℤ)^(v+E.size) ∣ a) : Weighted v (monomial E a) := by
  intro F
  by_cases hf : E = F
  · subst F; simpa using h
  · simp [coeff_monomial, hf]

/-- A coefficient times a known power of two pays for an output monomial. -/
theorem monomial_gain (v E F b g : ℕ) (a z : ℤ)
    (ha : (2 : ℤ)^(v+E.size) ∣ a)
    (hg : g+F.size ≤ E.size+b) :
    Weighted (v+g) (monomial F (a * (2:ℤ)^b * z)) := by
  apply weighted_monomial
  apply dvd_trans (pow_dvd_pow (2:ℤ) (by omega : v+g+F.size ≤ v+E.size+b))
  rw [pow_add]
  exact dvd_trans (mul_dvd_mul ha (dvd_refl ((2:ℤ)^b))) (dvd_mul_right _ z)

/-- Binomial form of a single contribution in Lemma R. -/
noncomputable def reducedTerm (m E i : ℕ) (a : ℤ) : Polynomial ℤ :=
  monomial (E/2+i) (a * (2:ℤ)^(2*i + (if E%2 = 0 then 1 else 0)) *
    ((Nat.choose (m+E/2+i+1) (2*i + (if E%2 = 0 then 1 else 0)) : ℕ):ℤ))

/-- Every non-leading even contribution gains two units of weight. -/
theorem reduced_even_gain (m e i v : ℕ) (a : ℤ)
    (ha : (2:ℤ)^(v+(2*e).size) ∣ a) (h : e ≠ 0 ∨ i ≠ 0) :
    Weighted (v+2) (reducedTerm m (2*e) i a) := by
  have hdiv : 2*e/2 = e := by omega
  simp only [reducedTerm, Nat.mul_mod_right, ite_true, hdiv]
  apply monomial_gain v (2*e) (e+i) (2*i+1) 2 a _ ha
  have hs := size_add_le e i
  have hi := size_le_self i
  rcases h with he | hi'
  · rw [size_double e he]
    omega
  · by_cases he : e = 0
    · subst e
      simp only [Nat.zero_add, Nat.size_zero]
      omega
    · rw [size_double e he]
      omega

/-- Odd contributions with i positive gain two units of weight. -/
theorem reduced_odd_tail_gain (m e i v : ℕ) (a : ℤ)
    (ha : (2:ℤ)^(v+(2*e+1).size) ∣ a) (hi : i ≠ 0) :
    Weighted (v+2) (reducedTerm m (2*e+1) i a) := by
  have hmod : (2*e+1)%2 ≠ 0 := by omega
  have hdiv : (2*e+1)/2 = e := by omega
  simp only [reducedTerm, hmod, ite_false, add_zero, hdiv]
  apply monomial_gain v (2*e+1) (e+i) (2*i) 2 a _ ha
  have hs := size_add_le e i
  have hh := size_le_self i
  rw [size_double_add_one]
  omega

/-- The leading odd contribution gains one unit of weight. -/
theorem reduced_odd_main_gain (m e v : ℕ) (a : ℤ)
    (ha : (2:ℤ)^(v+(2*e+1).size) ∣ a) :
    Weighted (v+1) (reducedTerm m (2*e+1) 0 a) := by
  have hmod : (2*e+1)%2 ≠ 0 := by omega
  have hdiv : (2*e+1)/2 = e := by omega
  simp only [reducedTerm, hmod, ite_false, add_zero, hdiv]
  norm_num only [mul_zero, pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
  apply weighted_monomial
  rw [size_double_add_one] at ha
  convert ha using 1
  congr 1
  omega

/-- The exceptional even term has one factor of two without any condition on m. -/
theorem reduced_zero_main_gain (m v : ℕ) (a : ℤ)
    (ha : (2:ℤ)^v ∣ a) : Weighted (v+1) (reducedTerm m 0 0 a) := by
  simp only [reducedTerm]
  norm_num only [Nat.zero_div, Nat.zero_mod, ite_true, mul_zero, zero_add, add_zero,
    pow_one, Nat.choose_one_right, Nat.cast_add, Nat.cast_one]
  apply monomial_gain v 0 0 1 1 a _ (by simpa using ha)
  simp

theorem reduced_term_gain (m E i v : ℕ) (a : ℤ)
    (ha : (2:ℤ)^(v+E.size) ∣ a) : Weighted (v+1) (reducedTerm m E i a) := by
  by_cases he : E%2 = 0
  · have hE : E = 2*(E/2) := by omega
    rw [hE] at ha ⊢
    by_cases h : E/2 ≠ 0 ∨ i ≠ 0
    · exact weighted_mono (reduced_even_gain m (E/2) i v a ha h) (by omega)
    · have he0 : E/2 = 0 := by tauto
      have hi0 : i = 0 := by tauto
      subst i
      simp only [he0, mul_zero, Nat.size_zero, add_zero] at ha ⊢
      exact reduced_zero_main_gain m v a ha
  · have hE : E = 2*(E/2)+1 := by omega
    rw [hE] at ha ⊢
    by_cases hi : i = 0
    · subst i; exact reduced_odd_main_gain m (E/2) v a ha
    · exact weighted_mono (reduced_odd_tail_gain m (E/2) i v a ha hi) (by omega)

/-- The explicit integral reduced operator. The finite cutoffs include all nonzero
binomial terms. Its identification with the series transfer is a separate obligation. -/
noncomputable def reduced (m : ℕ) (R : Polynomial ℤ) : Polynomial ℤ :=
  ∑ E ∈ R.support, ∑ i ∈ Finset.range (m+E/2+2), reducedTerm m E i (R.coeff E)

/-- Lemma W: one factor of two per halving for the explicit reduced operator. -/
theorem weighted_reduced (m v : ℕ) (R : Polynomial ℤ) (hR : Weighted v R) :
    Weighted (v+1) (reduced m R) := by
  apply weighted_sum
  intro E _
  apply weighted_sum
  intro i _
  exact reduced_term_gain m E i v (R.coeff E) (hR E)

noncomputable def reducedIter (m : ℕ) (R : Polynomial ℤ) : ℕ → Polynomial ℤ
  | 0 => R
  | j+1 => reduced m (reducedIter m R j)

/-- Iterated weight growth, without making any series-bridge assumption. -/
theorem weighted_reducedIter (m v j : ℕ) (R : Polynomial ℤ) (hR : Weighted v R) :
    Weighted (v+j) (reducedIter m R j) := by
  induction j with
  | zero => simpa [reducedIter] using hR
  | succ j ih => exact weighted_reduced m (v+j) _ ih

/-- Ordinary divisibility follows by forgetting the nonnegative bit-length term. -/
theorem weighted_coeff_dvd {v : ℕ} {R : Polynomial ℤ} (hR : Weighted v R) (E : ℕ) :
    (2:ℤ)^v ∣ R.coeff E :=
  dvd_trans (pow_dvd_pow _ (by omega)) (hR E)

/-- Remove exactly the i=0 odd terms and the exceptional E=i=0 term. -/
noncomputable def reducedTail (m : ℕ) (R : Polynomial ℤ) : Polynomial ℤ :=
  ∑ E ∈ R.support, ∑ i ∈ Finset.range (m+E/2+2),
    if i = 0 ∧ (E = 0 ∨ E%2 = 1) then 0 else reducedTerm m E i (R.coeff E)

/-- The error H in Lemma W gains two units of weight. -/
theorem weighted_reducedTail (m v : ℕ) (R : Polynomial ℤ) (hR : Weighted v R) :
    Weighted (v+2) (reducedTail m R) := by
  apply weighted_sum
  intro E _
  apply weighted_sum
  intro i _
  split_ifs with h
  · exact weighted_zero _
  · by_cases he : E%2 = 0
    · have hE : E = 2*(E/2) := by omega
      have ha := hR E
      rw [hE] at ha ⊢
      apply reduced_even_gain _ _ _ _ _ ha
      omega
    · have hE : E = 2*(E/2)+1 := by omega
      have ha := hR E
      rw [hE] at ha ⊢
      apply reduced_odd_tail_gain _ _ _ _ _ ha
      omega

theorem coeff_reducedTerm_zero (m E i : ℕ) (a : ℤ) :
    (reducedTerm m E i a).coeff 0 =
      (if E = 0 ∧ i = 0 then a*2*((m:ℤ)+1) else 0) +
      (if E = 1 ∧ i = 0 then a else 0) := by
  by_cases h : E/2+i = 0
  · have hi : i = 0 := by omega
    have he : E ≤ 1 := by omega
    subst i
    interval_cases E <;> simp [reducedTerm, coeff_monomial]
  · have h0 : ¬ (E = 0 ∧ i = 0) := by omega
    have h1 : ¬ (E = 1 ∧ i = 0) := by omega
    simp only [reducedTerm, coeff_monomial, ite_eq_right h, ite_eq_right h0, ite_eq_right h1, add_zero]

/-- Exact constant coefficient, including the exceptional two input monomials. -/
theorem coeff_reduced_zero (m : ℕ) (R : Polynomial ℤ) :
    (reduced m R).coeff 0 = 2*((m:ℤ)+1)*R.coeff 0 + R.coeff 1 := by
  simp only [reduced, finsetSum_coeff, coeff_reducedTerm_zero, Finset.sum_add_distrib]
  have hi (E : ℕ) : 0 ∈ Finset.range (m+E/2+2) := by simp
  simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', hi, ite_true]
  simp only [Finset.sum_ite_eq', Polynomial.mem_support_iff]
  split_ifs <;> simp_all <;> ring

/-- The leading part isolated in Lemma W. -/
noncomputable def reducedMain (m : ℕ) (R : Polynomial ℤ) : Polynomial ℤ :=
  ∑ E ∈ R.support, ∑ i ∈ Finset.range (m+E/2+2),
    if i = 0 ∧ (E = 0 ∨ E%2 = 1) then reducedTerm m E i (R.coeff E) else 0

theorem reduced_main_tail (m : ℕ) (R : Polynomial ℤ) :
    reduced m R = reducedMain m R + reducedTail m R := by
  simp only [reduced, reducedMain, reducedTail, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro E _
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp
end Ulas.Round3
