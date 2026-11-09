import CatalanTop
import RiccatiScale

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSimpArgs false

noncomputable section
namespace JacobiShifted.SourceBridge
open MvPolynomial
open JacobiShifted.ParameterDegree

@[simp] theorem rationalScalar_eq_C (q : ℚ) : rationalScalar q=MvPolynomial.C (rationalBase q) := by
  simp [rationalScalar,paramEmbed]

theorem subVar_homogeneous (i : Fin 2) : (subVar i).IsHomogeneous 1 := by
  have h0 := isHomogeneous_X MidpointRational.QAlg (0 : Fin 2)
  have h1 := isHomogeneous_X MidpointRational.QAlg (1 : Fin 2)
  by_cases hi : i=0
  · simpa only [subVar, hi, ite_true, rationalScalar_eq_C] using (h0.add h1).C_mul (rationalBase (1/2))
  · simpa only [subVar, hi, ite_false, rationalScalar_eq_C] using (h0.sub h1).C_mul (rationalBase (1/2))

theorem scale_homogeneous (f : Midpoint.Param) (n : ℕ) (hf : f.IsHomogeneous n) :
    (scale f).IsHomogeneous n := by
  simpa only [scale, MvPolynomial.coe_eval₂Hom, one_mul] using hf.eval₂ (MvPolynomial.C.comp MidpointRational.lift) subVar
    (fun c => isHomogeneous_C _ (MidpointRational.lift c)) subVar_homogeneous

/-- Rational linear substitution preserves each homogeneous layer; no integral
coefficient divisibility is inferred from the halves. -/
theorem scale_homogeneousComponent (n : ℕ) (f : Midpoint.Param) :
    scale (homogeneousComponent n f)=homogeneousComponent n (scale f) := by
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => simp only [map_add, hf, hg]
  | monomial d c =>
    have hh : (monomial d c : Midpoint.Param).IsHomogeneous d.degree := isHomogeneous_monomial c rfl
    rw [homogeneousComponent_of_mem hh, homogeneousComponent_of_mem (scale_homogeneous _ _ hh)]
    split_ifs <;> simp

theorem scaledH_coeff_eq_zero (n : ℕ) (a : Fin 2 →₀ ℕ)
    (ha : (n+1)/2 < a.degree) : (scaledH n).coeff a=0 := by
  have hz := homogeneousComponent_eq_zero a.degree (Midpoint.h n) (lt_of_le_of_lt (h_totalDegree n) ha)
  have he := congrArg (fun p : A => p.coeff a) (scale_homogeneousComponent a.degree (Midpoint.h n))
  rw [hz, map_zero, AddMonoidAlgebra.coeff_zero, coeff_homogeneousComponent, ite_eq_left rfl] at he
  exact he.symm

theorem scaledH_odd_top (r : ℕ) (hr : 1≤r) :
    homogeneousComponent r (scaledH (2*r-1))=
      MvPolynomial.C ((-1 : MidpointRational.QAlg)^(r-1)*(catalan (r-1) : MidpointRational.QAlg))*S^r := by
  rw [scaledH, ← scale_homogeneousComponent, h_odd_top r hr, map_mul, map_pow, scale_C]
  have hp : scale Midpoint.P=S := by simpa only [scaledH, Midpoint.h_one] using scaledH_one
  rw [hp]
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast]

/-- Coefficient of a pure power in an arbitrary two-term linear form. -/
theorem linear_power_pure (a b : MidpointRational.QAlg) (r : ℕ) :
    ((MvPolynomial.C a*MvPolynomial.X 0+MvPolynomial.C b*MvPolynomial.X 1 : A)^r).coeff
      (Finsupp.single 0 r)=a^r := by
  classical
  rw [add_pow]
  simp only [coeff_sum]
  rw [Finset.sum_eq_single r]
  · simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one]
    rw [mul_pow, ← map_pow MvPolynomial.C, MvPolynomial.C_mul_X_pow_eq_monomial]
    simp only [MvPolynomial.coeff_monomial, ite_eq_left rfl, ite_true]
  · intro j hj hjr
    have hjr' : j<r := by have := Finset.mem_range.mp hj; omega
    have hne : Finsupp.single (0 : Fin 2) j+Finsupp.single 1 (r-j)≠Finsupp.single 0 r := by
      intro he
      have he1 := congrArg (fun d : Fin 2 →₀ ℕ => d 1) he
      simp only [Finsupp.add_apply,Finsupp.single_eq_of_ne (by decide : (1 : Fin 2)≠0), Finsupp.single_eq_same] at he1
      omega
    simp only [mul_pow, ← map_pow MvPolynomial.C, MvPolynomial.C_mul_X_pow_eq_monomial,
      MvPolynomial.monomial_mul_monomial]
    rw [mul_comm _ ((r.choose j : ℕ) : A)]
    rw [show ((r.choose j : ℕ) : A)=MvPolynomial.C ((r.choose j : ℕ) : MidpointRational.QAlg) by simp, MvPolynomial.coeff_C_mul]
    simp only [MvPolynomial.coeff_monomial, ite_eq_right hne, mul_zero]
  · simp

theorem S_linear : S=
    MvPolynomial.C (rationalBase (1/2)*(MidpointRational.w*t))*MvPolynomial.X 0+
    MvPolynomial.C (rationalBase (1/2)*(MidpointRational.w*tInv))*MvPolynomial.X 1 := by
  simp only [S,t,tInv,rationalScalar_eq_C,map_mul,map_add,map_sub,map_pow]
  ring

/-- Literal pure-u top coefficient after the specified rational substitution. -/
theorem scaledH_odd_pure_u (r : ℕ) (hr : 1≤r) :
    (scaledH (2*r-1)).coeff (Finsupp.single 0 r)=
      rationalBase (((-1 : ℚ)^(r-1)*(catalan (r-1) : ℚ))/(2 : ℚ)^r)*
        (MidpointRational.w*t)^r := by
  have he := congrArg (fun p : A => p.coeff (Finsupp.single 0 r)) (scaledH_odd_top r hr)
  rw [coeff_homogeneousComponent, Finsupp.degree_single, ite_eq_left rfl, coeff_C_mul,
    S_linear, linear_power_pure, mul_pow] at he
  rw [he]
  have hcast : ((-1 : MidpointRational.QAlg)^(r-1)*(catalan (r-1) : MidpointRational.QAlg))=
      rationalBase ((-1 : ℚ)^(r-1)*(catalan (r-1) : ℚ)) := by simp
  rw [hcast, ← mul_assoc, ← map_pow, ← map_mul]
  congr 2
  rw [div_pow]
  ring

end JacobiShifted.SourceBridge
