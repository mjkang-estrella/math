import PartitionExpansion

set_option autoImplicit false
set_option warningAsError true

namespace PeakonCoefficients

open Matrix PowerSeries

variable {K : Type*} [Field K]
variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

theorem rawHamiltonian_vanish (u v : n → K) (gamma : K) (k : ℕ)
    (hk : Fintype.card n < k) : rawHamiltonian u v gamma k = 0 := by
  have hB := strict_upper_power_zero (upperKernel u v)
    (upperKernel_triangular u v) (upperKernel_diagonal u v)
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (show Fintype.card n ≤ k - 1 by omega)
  unfold rawHamiltonian
  rw [hj, pow_add, hB, zero_mul, Matrix.mul_zero, Matrix.trace_zero, mul_zero]

omit [Fintype n] [DecidableEq n] [LinearOrder n] in
theorem finiteHamiltonianSeries_coeff (s : Finset ℕ) (h : ℕ → K) (k : ℕ) :
    coeff k (finiteHamiltonianSeries s h) = if k ∈ s then h k / (k : K) else 0 := by
  simp [finiteHamiltonianSeries, coeff_monomial]

omit [Fintype n] [DecidableEq n] [LinearOrder n] in
theorem coeff_pow_congr_upto (f g : PowerSeries K) (m j : ℕ)
    (h : ∀ k ≤ m, coeff k f = coeff k g) : coeff m (f ^ j) = coeff m (g ^ j) := by
  have ht : trunc (m + 1) f = trunc (m + 1) g := by
    apply Polynomial.ext
    intro k
    rw [coeff_trunc, coeff_trunc]
    by_cases hk : k < m + 1
    · rw [ite_eq_left hk, ite_eq_left hk]
      exact h k (by omega)
    · rw [ite_eq_right hk, ite_eq_right hk]
  have hp : trunc (m + 1) (f ^ j) = trunc (m + 1) (g ^ j) := by
    rw [← trunc_trunc_pow f, ← trunc_trunc_pow g, ht]
  have hc := congrArg (fun P : Polynomial K => P.coeff m) hp
  simpa only [coeff_trunc, Nat.lt_succ_self, ↓reduceIte] using hc

theorem finiteHamiltonianSeries_card_to_order (u v : n → K) (gamma : K) (m j : ℕ) :
    coeff m (finiteHamiltonianSeries (Finset.Icc 1 (Fintype.card n))
        (rawHamiltonian u v gamma) ^ j) =
      coeff m (finiteHamiltonianSeries (Finset.Icc 1 m) (rawHamiltonian u v gamma) ^ j) := by
  apply coeff_pow_congr_upto
  intro k hk
  rw [finiteHamiltonianSeries_coeff, finiteHamiltonianSeries_coeff]
  by_cases hk0 : k = 0
  · subst k
    simp
  · have hk1 : 1 ≤ k := by omega
    have hkm : k ∈ Finset.Icc 1 m := Finset.mem_Icc.mpr ⟨hk1, hk⟩
    rw [ite_eq_left hkm]
    by_cases hkn : k ≤ Fintype.card n
    · rw [ite_eq_left (Finset.mem_Icc.mpr ⟨hk1, hkn⟩)]
    · rw [ite_eq_right (by simpa only [Finset.mem_Icc, not_and] using
        fun _ : 1 ≤ k => hkn), rawHamiltonian_vanish u v gamma k (by omega), zero_div]

end PeakonCoefficients
