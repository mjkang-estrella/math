import UlasEven5Kummer
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
open Polynomial
namespace Ulas.Even5
open Ulas.Round4

theorem rho_coeff_dvd (k E : ℕ) (hk : 1 ≤ k) :
    (2:ℤ)^(3+2*padicValNat 2 k+E) ∣ (rho k).coeff E := by
  simp only [rho,pow_two,coeff_ofNat_mul,coeff_mul,Finset.mul_sum]
  apply Finset.dvd_sum
  intro p hp
  have he := Finset.mem_antidiagonal.mp hp
  have hh := mul_dvd_mul (by norm_num : (2:ℤ)^3 ∣ 8)
    (mul_dvd_mul (u_coeff_dvd k p.1 hk) (u_coeff_dvd k p.2 hk))
  rw [← pow_add, ← pow_add] at hh
  convert hh using 1 <;> congr 1 <;> omega

theorem rho_one_dvd (k : ℕ) (hk : 1 ≤ k) :
    (2:ℤ)^(3+2*padicValNat 2 k+2) ∣ (rho k).coeff 1 := by
  have he : (rho k).coeff 1 =
      16*((u ((k:ℤ)-1)).coeff 0*(u ((k:ℤ)-1)).coeff 1) := by
    simp [rho,pow_two,coeff_mul,Finset.Nat.antidiagonal_succ,
      Finset.Nat.antidiagonal_zero]
    ring
  rw [he]
  have hh := mul_dvd_mul (by norm_num : (2:ℤ)^4 ∣ 16)
    (mul_dvd_mul (u_coeff_dvd k 0 hk) (u_coeff_dvd k 1 hk))
  rw [← pow_add, ← pow_add] at hh
  convert hh using 1 <;> congr 1 <;> omega

theorem size_le_self (E : ℕ) : E.size ≤ E := by
  exact Nat.size_le.mpr (Nat.lt_two_pow_self)

theorem exceptional_size (i : ℕ) (hi : 2 ≤ i) : i+1 ≤ 2^i-1 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hi
  induction j with
  | zero => norm_num
  | succ j ih => rw [show 2+(j+1)=(2+j)+1 by omega,pow_succ]; omega

theorem rho_invariant (k : ℕ) (hk : 1 ≤ k) :
    EvenInvariant (3+2*padicValNat 2 k) (rho k) := by
  refine ⟨?_,?_,?_⟩
  · intro E
    exact dvd_trans (pow_dvd_pow _ (by have := size_le_self E; omega)) (rho_coeff_dvd k E hk)
  · rw [rho_zero]
    have hz : (k:ℤ) ≠ 0 := by omega
    have hv : padicValInt 2 (8*(k:ℤ)^2) = 3+2*padicValNat 2 k := by
      rw [padicValInt.mul (by norm_num) (pow_ne_zero _ hz),pow_two, padicValInt.mul hz hz]
      have h8 : padicValInt 2 (8:ℤ) = 3 := by
        change padicValNat 2 (2^3) = 3
        exact padicValNat.prime_pow 3
      rw [h8, padicValInt.of_nat]
      omega
    intro hd
    have hh := ((padicValInt_dvd_iff (p := 2) _ _).mp hd).resolve_left
      (mul_ne_zero (by norm_num) (pow_ne_zero _ hz))
    omega
  · intro i hi
    by_cases he : i = 1
    · subst i; norm_num; exact rho_one_dvd k hk
    · have hh := exceptional_size i (by omega)
      exact dvd_trans (pow_dvd_pow _ (by omega)) (rho_coeff_dvd k (2^i-1) hk)

/-- Adding a polynomial one invariant level higher preserves the lower invariant. -/
theorem invariant_add {v : ℕ} {R S : Polynomial ℤ}
    (hr : EvenInvariant v R) (hs : EvenInvariant (v+1) S) : EvenInvariant v (R+S) := by
  refine ⟨?_,?_,?_⟩
  · intro E
    rw [coeff_add]
    exact dvd_add (hr.1 E) (dvd_trans (pow_dvd_pow _ (by omega)) (hs.1 E))
  · rw [coeff_add]
    intro hd
    apply hr.2.1
    have hh := dvd_sub hd (show (2:ℤ)^(v+1) ∣ S.coeff 0 by simpa using hs.1 0)
    convert hh using 1 <;> ring
  · intro i hi
    rw [coeff_add]
    exact dvd_add (hr.2.2 i hi) (dvd_trans (pow_dvd_pow _ (by omega)) (hs.2.2 i hi))

theorem evenInitialization_proved : EvenInitialization := by
  intro k hk
  refine ⟨initial k, initial_represents k, ?_⟩
  exact invariant_add (rho_invariant k hk)
    (invariant_step (2*k) _ _ (by omega) (rho_invariant k hk))

theorem evenFormula_proved : EvenFormula := evenFormula_of_initialization evenInitialization_proved
end Ulas.Even5
