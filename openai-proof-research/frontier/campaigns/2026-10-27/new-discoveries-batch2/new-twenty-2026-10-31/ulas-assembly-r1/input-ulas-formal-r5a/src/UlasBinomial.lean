import UlasBridge
open Polynomial
namespace Ulas.Round4
noncomputable def binA (m : ℕ) : Polynomial ℤ :=
  ∑ i ∈ Finset.range (m+2), monomial i ((2:ℤ)^(2*i+1)*(Nat.choose (m+i+1) (2*i+1):ℤ))
noncomputable def binB (m : ℕ) : Polynomial ℤ :=
  ∑ i ∈ Finset.range (m+2), monomial i ((2:ℤ)^(2*i)*(Nat.choose (m+i+1) (2*i):ℤ))
theorem coeff_binA (m i : ℕ) : (binA m).coeff i =
    (2:ℤ)^(2*i+1)*(Nat.choose (m+i+1) (2*i+1):ℤ) := by
  simp only [binA, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · have hi : m+2 ≤ i := by simpa using h
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
theorem coeff_binB (m i : ℕ) : (binB m).coeff i =
    (2:ℤ)^(2*i)*(Nat.choose (m+i+1) (2*i):ℤ) := by
  simp only [binB, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · have hi : m+2 ≤ i := by simpa using h
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

theorem binA_succ (m : ℕ) : binA (m+1) = binA m+2*binB m := by
  ext i
  rw [coeff_add, coeff_ofNat_mul, coeff_binA, coeff_binA, coeff_binB]
  rw [show m+1+i+1 = (m+i+1)+1 by omega, Nat.choose_succ_succ,
    Nat.cast_add]
  ring

theorem binB_succ (m : ℕ) : binB (m+1) = binB m+2*X*binA (m+1) := by
  ext i
  cases i with
  | zero => simp [coeff_binB]
  | succ i =>
    rw [coeff_add]
    have hmul : (2*X*binA (m+1)).coeff (i+1) = 2*(binA (m+1)).coeff i := by
      rw [mul_assoc, coeff_ofNat_mul, coeff_X_mul]
    rw [hmul, coeff_binB, coeff_binB, coeff_binA]
    rw [show m+1+(i+1)+1 = (m+i+2)+1 by omega,
      show 2*(i+1) = (2*i+1)+1 by omega, Nat.choose_succ_succ, Nat.cast_add]
    simp only [show m+(i+1)+1 = m+i+2 by omega,
      show m+1+i+1 = m+i+2 by omega]
    ring

theorem binA_zero : binA 0 = 2 := by norm_num [binA, Finset.sum_range_succ, monomial_zero_left]
theorem binB_zero : binB 0 = 1+4*X := by
  norm_num [binB, Finset.sum_range_succ, monomial_zero_left]
  simpa using (C_mul_X_eq_monomial (a := (4:ℤ))).symm

theorem reducedPair_zero (m : ℕ) :
    reducedPair m 0 = (binA m, binB m-X*binA m) := by
  induction m with
  | zero => simp [reducedPair, binA_zero, binB_zero]; ring
  | succ m ih =>
    simp only [reducedPair, ih, binA_succ, binB_succ, Prod.mk.injEq]
    constructor <;> ring

theorem reducedPair_y (m E : ℕ) : reducedPair m (E+1) =
    (X*(reducedPair m E).1+(reducedPair m E).2,
      X*(1+X)*(reducedPair m E).1+X*(reducedPair m E).2) := by
  induction m with
  | zero => simp [reducedPair]
  | succ m ih => simp only [reducedPair, ih, Prod.mk.injEq]; constructor <;> ring

theorem reducedPair_two (m E : ℕ) : reducedPair m (E+2) =
    (X*(reducedPair (m+1) E).1, X*(reducedPair (m+1) E).2) := by
  rw [show E+2 = (E+1)+1 by omega, reducedPair_y, reducedPair_y]
  simp only [reducedPair, Prod.mk.injEq]
  constructor <;> ring

theorem reducedPair_even (m e : ℕ) : (reducedPair m (2*e)).1 = X^e*binA (m+e) := by
  induction e generalizing m with
  | zero => simp [reducedPair_zero]
  | succ e ih =>
    rw [show 2*(e+1) = 2*e+2 by omega, reducedPair_two]
    simp only [ih, show m+1+e = m+(e+1) by omega]
    ring

theorem reducedPair_one (m : ℕ) : (reducedPair m 1).1 = binB m := by
  rw [show 1 = 0+1 from rfl, reducedPair_y, reducedPair_zero]
  simp

theorem reducedPair_odd (m e : ℕ) : (reducedPair m (2*e+1)).1 = X^e*binB (m+e) := by
  induction e generalizing m with
  | zero => simp [reducedPair_one]
  | succ e ih =>
    rw [show 2*(e+1)+1 = (2*e+1)+2 by omega, reducedPair_two]
    simp only [ih, show m+1+e = m+(e+1) by omega]
    ring

theorem reducedPair_binomial (m E : ℕ) :
    (reducedPair m E).1 = ∑ i ∈ Finset.range (m+E/2+2),
      Round3.reducedTerm m E i 1 := by
  by_cases he : E%2 = 0
  · have hE : E = 2*(E/2) := by omega
    rw [hE, reducedPair_even]
    simp only [Round3.reducedTerm, show 2*(E/2)/2 = E/2 by omega, Nat.mul_mod_right, ite_true,
      one_mul, binA, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [X_pow_mul_monomial, Nat.add_comm]
  · have hE : E = 2*(E/2)+1 := by omega
    rw [hE, reducedPair_odd]
    simp only [Round3.reducedTerm, show (2*(E/2)+1)/2 = E/2 by omega,
      show (2*(E/2)+1)%2 = 1 by omega, Nat.one_ne_zero, ite_false,
      add_zero, one_mul, binB, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [X_pow_mul_monomial, Nat.add_comm]

theorem binomialIdentification : BinomialIdentification := by
  intro m R
  unfold recursiveReduced Round3.reduced
  apply Finset.sum_congr rfl
  intro E _
  rw [reducedPair_binomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Round3.reducedTerm, one_mul, C_mul_monomial]
  congr 1
  ring

/-- Lemma R, with the frozen round-3 binomial operator, unconditionally. -/
theorem lemma_R_unconditional (m : ℕ) (R : Polynomial ℤ) :
    Ulas.sectionEven (Ulas.w^m*(y*(1+y)*ev R)) =
      y*(1+y)*ev (Round3.reduced m R) :=
  lemma_R binomialIdentification m R
end Ulas.Round4
