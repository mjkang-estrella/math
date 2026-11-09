import CayleyPolynomials
namespace ContactPilot
noncomputable section
open MvPolynomial
set_option linter.unusedSimpArgs false
private abbrev J : Poly₂ := C Complex.I
private def fm : Poly₂ := J*(1-W)*(J*(1-Z)) - J*(1-W)*(1+Z) - (1+Z)*(1+W)
private def fp : Poly₂ := J*(1-W)*(J*(1-Z)) + J*(1-W)*(1+Z) - (1+Z)*(1+W)
private abbrev k : MvPolynomial (Fin 1) ℂ := X 0
private abbrev jm : MvPolynomial (Fin 1) ℂ := C Complex.I
private def u (s : ℂ) : MvPolynomial (Fin 1) ℂ := C (-2-s*Complex.I)*k + C (s*Complex.I)
private def v (s : ℂ) : MvPolynomial (Fin 1) ℂ := C (-s*Complex.I)*k + C (-2+s*Complex.I)
private theorem uv_relprime (s : ℂ) (hs : s^2 = 1) : IsRelPrime (u s) (v s) := by
  intro d hu hv
  have hi : C (s*Complex.I)*u s + C (-2-s*Complex.I)*v s = (4 : MvPolynomial (Fin 1) ℂ) := by
    simp only [u,v, mul_add, ←map_mul, ←map_add]
    ring_nf
    simp only [←map_pow, ←map_mul, ←map_add]
    norm_num [Complex.I_sq, hs, map_ofNat]
    ring_nf
  have hd : d ∣ (4 : MvPolynomial (Fin 1) ℂ) := by
    rw [←hi]
    exact dvd_add (dvd_mul_of_dvd_right hu _) (dvd_mul_of_dvd_right hv _)
  exact isUnit_of_dvd_unit hd ((isUnit_iff_ne_zero.mpr (by norm_num : (4:ℂ) ≠ 0)).map C)
private theorem u_ne_zero (s : ℂ) (hs : s ≠ 0) : u s ≠ 0 := by
  intro h
  have he := congrArg (eval (fun _ : Fin 1 => (0:ℂ))) h
  simp [u, mul_ne_zero hs Complex.I_ne_zero] at he
private theorem mapped_fm :
    MvPolynomial.finSuccEquiv ℂ 1 fm = Polynomial.C (u (-1)) * Polynomial.X + Polynomial.C (v (-1)) := by
  simp only [fm, J, Z, W, map_sub, map_mul, map_add, map_one,
    show (1 : Fin 2) = (0 : Fin 1).succ from rfl,
    finSuccEquiv_X_zero, finSuccEquiv_X_succ]
  simp [u, v, k, finSuccEquiv_apply]
  ring_nf
  norm_num [←map_pow, ←map_mul, ←map_add, Complex.I_sq, map_ofNat]
  ring
private theorem mapped_fp :
    MvPolynomial.finSuccEquiv ℂ 1 fp = Polynomial.C (u 1) * Polynomial.X + Polynomial.C (v 1) := by
  simp only [fp, J, Z, W, map_sub, map_mul, map_add, map_one,
    show (1 : Fin 2) = (0 : Fin 1).succ from rfl,
    finSuccEquiv_X_zero, finSuccEquiv_X_succ]
  simp [u, v, k, finSuccEquiv_apply]
  ring_nf
  norm_num [←map_pow, ←map_mul, ←map_add, Complex.I_sq, map_ofNat]
  ring
private theorem fm_irreducible : Irreducible fm := by
  apply (MulEquiv.irreducible_iff (f := finSuccEquiv ℂ 1)).mp
  rw [mapped_fm]
  exact Polynomial.irreducible_C_mul_X_add_C (u_ne_zero (-1) (by norm_num))
    (uv_relprime (-1) (by norm_num))
private theorem fp_irreducible : Irreducible fp := by
  apply (MulEquiv.irreducible_iff (f := finSuccEquiv ℂ 1)).mp
  rw [mapped_fp]
  exact Polynomial.irreducible_C_mul_X_add_C (u_ne_zero 1 (by norm_num))
    (uv_relprime 1 (by norm_num))
private theorem b_irreducible : Irreducible (1+Z) := by
  apply (MulEquiv.irreducible_iff (f := finSuccEquiv ℂ 1)).mp
  simpa [Z, finSuccEquiv_X_zero, add_comm, sub_neg_eq_add] using
    (Polynomial.irreducible_X_sub_C (-1 : MvPolynomial (Fin 1) ℂ))
private theorem fm_not_dvd : ¬ fm ∣ cayleyQ := by
  rintro ⟨t, ht⟩
  have h := congrArg (fun p => eval₂ p 1 (-Complex.I)) ht
  norm_num [eval₂, cayleyQ, fm, J, Z, W, Complex.I_sq, map_ofNat, Complex.ext_iff] at h
private theorem fp_not_dvd : ¬ fp ∣ cayleyQ := by
  rintro ⟨t, ht⟩
  have h := congrArg (fun p => eval₂ p 1 Complex.I) ht
  norm_num [eval₂, cayleyQ, fp, J, Z, W, Complex.I_sq, map_ofNat, Complex.ext_iff] at h
private theorem b_not_dvd : ¬ (1+Z) ∣ cayleyQ := by
  rintro ⟨t, ht⟩
  have h := congrArg (fun p => eval₂ p (-1) 0) ht
  norm_num [eval₂, cayleyQ, J, Z, W, Complex.I_sq, map_ofNat, Complex.ext_iff] at h
private theorem cayley_reduced : IsRelPrime cayleyN cayleyQ := by
  have h₀ := b_irreducible.isRelPrime_iff_not_dvd.mpr b_not_dvd
  have h₁ := fm_irreducible.isRelPrime_iff_not_dvd.mpr fm_not_dvd
  have h₂ := fp_irreducible.isRelPrime_iff_not_dvd.mpr fp_not_dvd
  exact (h₀.mul_left h₁).mul_left h₂

theorem bidisk_pair_reduced : ∀ d : Poly₂,
    d ∣ bidiskNumerator → d ∣ bidiskDenominator → IsUnit d := by
  intro d hp hm
  have hq : d ∣ cayleyQ := by
    have h := dvd_add hp hm
    have he : bidiskNumerator + bidiskDenominator = cayleyQ * 2 := by
      unfold bidiskNumerator bidiskDenominator; ring
    rw [he] at h
    have hu : IsUnit (2 : Poly₂) :=
      (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℂ) ≠ 0)).map C
    exact hu.dvd_mul_right.mp h
  have hn : d ∣ cayleyN := by
    have h := dvd_sub hp hm
    have he : bidiskNumerator - bidiskDenominator = cayleyN * C (2*Complex.I) := by
      unfold bidiskNumerator bidiskDenominator
      simp only [map_mul, map_ofNat]; ring
    rw [he] at h
    have hu : IsUnit (C (2*Complex.I) : Poly₂) :=
      (isUnit_iff_ne_zero.mpr (mul_ne_zero (by norm_num) Complex.I_ne_zero)).map C
    exact hu.dvd_mul_right.mp h
  exact cayley_reduced hn hq
end
end ContactPilot
