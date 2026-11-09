import LiteralMidpoint
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option warningAsError true
set_option linter.unnecessarySeqFocus false

noncomputable section
namespace JacobiShifted.SourceBridge

def deltaA : A →+ A := BinaryFiltration.coefficientOperator MidpointRational.delta

@[simp] theorem deltaA_coeff (p : A) (m : Fin 2 →₀ ℕ) :
    (deltaA p).coeff m=MidpointRational.delta (p.coeff m) := rfl

@[simp] theorem deltaA_monomial (m : Fin 2 →₀ ℕ) (a : MidpointRational.QAlg) :
    deltaA (MvPolynomial.monomial m a)=MvPolynomial.monomial m (MidpointRational.delta a) := by
  apply MvPolynomial.ext
  intro k
  simp only [deltaA_coeff, MvPolynomial.coeff_monomial]
  split_ifs <;> simp

@[simp] theorem deltaA_C (a : MidpointRational.QAlg) :
    deltaA (MvPolynomial.C a)=MvPolynomial.C (MidpointRational.delta a) :=
  deltaA_monomial 0 a

theorem deltaA_mul (a b : A) : deltaA (a*b)=deltaA a*b+a*deltaA b := by
  induction a using MvPolynomial.induction_on' with
  | add a b ha hb => simp only [add_mul, map_add, ha, hb]; abel
  | monomial m a =>
    induction b using MvPolynomial.induction_on' with
    | add a b ha hb => simp only [mul_add, map_add, ha, hb]; abel
    | monomial n b =>
      simp only [MvPolynomial.monomial_mul_monomial, deltaA_monomial,
        MidpointRational.partial_mul, map_add]

@[simp] theorem delta_rationalBase (q : ℚ) :
    MidpointRational.delta (rationalBase q)=0 := by
  apply QuadraticAlgebra.ext <;> simp [rationalBase, MidpointRational.C, MidpointRational.delta]

@[simp] theorem deltaA_paramEmbed (p : QPoly) : deltaA (paramEmbed p)=0 := by
  apply MvPolynomial.ext
  intro m
  simp only [deltaA_coeff, paramEmbed, MvPolynomial.coeff_map, delta_rationalBase]
  rfl

@[simp] theorem deltaA_one : deltaA 1=0 := by
  have h := deltaA_paramEmbed 1
  simpa using h

def deltaG : G →+ G where
  toFun z := ⟨deltaA z.re,deltaA z.im⟩
  map_zero' := by apply QuadraticAlgebra.ext <;> simp
  map_add' a b := by apply QuadraticAlgebra.ext <;> simp

@[simp] theorem deltaG_re (z : G) : (deltaG z).re=deltaA z.re := rfl
@[simp] theorem deltaG_im (z : G) : (deltaG z).im=deltaA z.im := rfl

theorem deltaG_mul (a b : G) : deltaG (a*b)=deltaG a*b+a*deltaG b := by
  apply QuadraticAlgebra.ext <;> simp [deltaA_mul, map_add] <;> ring

@[simp] theorem deltaG_coeffEmbed (p : QPoly) : deltaG (coeffEmbed p)=0 := by
  apply QuadraticAlgebra.ext <;> simp [coeffEmbed, gaussianEmbed]

def imaginaryUnit : G := ⟨0,1⟩

@[simp] theorem imaginaryUnit_sq : imaginaryUnit^2 = -1 := by
  apply QuadraticAlgebra.ext <;>
    simp [imaginaryUnit, pow_two, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

@[simp] theorem deltaG_imaginaryUnit : deltaG imaginaryUnit=0 := by
  apply QuadraticAlgebra.ext <;> simp [imaginaryUnit]

@[simp] theorem deltaG_one : deltaG 1=0 := by
  apply QuadraticAlgebra.ext <;>
    simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem delta_t : MidpointRational.delta t= -(MidpointRational.w*t) := by
  simp only [t, map_add, MidpointRational.partial_w, MidpointRational.partial_x]
  rw [← MidpointRational.w_sq]
  ring

theorem delta_tInv : MidpointRational.delta tInv=MidpointRational.w*tInv := by
  simp only [tInv, map_sub, MidpointRational.partial_w, MidpointRational.partial_x]
  rw [← MidpointRational.w_sq]
  ring

theorem xi_eta_curve : 2*xi*eta=xi+eta := by
  have h : MvPolynomial.C t * MvPolynomial.C tInv=(1 : A) := by
    rw [← map_mul, t_mul_tInv, map_one]
  have hh : rationalScalar ((2 : ℚ)⁻¹)+rationalScalar ((2 : ℚ)⁻¹)=(1 : A) := by
    simp only [rationalScalar, ← map_add]
    norm_num
  apply QuadraticAlgebra.ext <;>
    simp [xi, eta, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  · linear_combination 2*(rationalScalar ((2 : ℚ)⁻¹))^2*h +
      (2*rationalScalar ((2 : ℚ)⁻¹))*hh
  · linear_combination (rationalScalar ((2 : ℚ)⁻¹)*(MvPolynomial.C t-MvPolynomial.C tInv))*hh

@[simp] theorem deltaA_rationalScalar (q : ℚ) : deltaA (rationalScalar q)=0 :=
  deltaA_paramEmbed (MvPolynomial.C q)

theorem half_twice : 2*rationalScalar (1/2)=(1 : A) := by
  have h : rationalScalar (1/2)+rationalScalar (1/2)=(1 : A) := by
    simp only [rationalScalar, ← map_add]
    norm_num
  simpa only [two_mul] using h

theorem t_square : t^2+1=2*MidpointRational.w*t := by
  dsimp [t]
  calc
    _ = 2*MidpointRational.w*(MidpointRational.w+MidpointRational.x) +
      (1+MidpointRational.x^2-MidpointRational.w^2) := by ring
    _ = _ := by rw [MidpointRational.w_sq]; ring

theorem deltaG_xi : deltaG xi=imaginaryUnit*xi*(xi-1) := by
  have hh := half_twice
  have ht := congrArg (MvPolynomial.C : MidpointRational.QAlg →+* A) t_square
  simp only [map_add, map_pow, map_one, map_mul, map_ofNat] at ht
  simp only [one_div] at hh
  apply QuadraticAlgebra.ext <;>
    simp [xi, imaginaryUnit, deltaA_mul, delta_t,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · linear_combination (rationalScalar ((2 : ℚ)⁻¹)*MvPolynomial.C t)*hh
  · linear_combination (rationalScalar ((2 : ℚ)⁻¹))^2*ht +
      rationalScalar ((2 : ℚ)⁻¹)*(MvPolynomial.C MidpointRational.w*MvPolynomial.C t-1)*hh

theorem tInv_square : tInv^2+1=2*MidpointRational.w*tInv := by
  dsimp [tInv]
  calc
    _ = 2*MidpointRational.w*(MidpointRational.w-MidpointRational.x) +
      (1+MidpointRational.x^2-MidpointRational.w^2) := by ring
    _ = _ := by rw [MidpointRational.w_sq]; ring

theorem deltaG_eta : deltaG eta=imaginaryUnit*eta*(eta-1) := by
  have hh := half_twice
  have ht := congrArg (MvPolynomial.C : MidpointRational.QAlg →+* A) tInv_square
  simp only [map_add, map_pow, map_one, map_mul, map_ofNat] at ht
  simp only [one_div] at hh
  apply QuadraticAlgebra.ext <;>
    simp [eta, imaginaryUnit, deltaA_mul, delta_tInv,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · linear_combination -(rationalScalar ((2 : ℚ)⁻¹)*MvPolynomial.C tInv)*hh
  · linear_combination (rationalScalar ((2 : ℚ)⁻¹))^2*ht +
      rationalScalar ((2 : ℚ)⁻¹)*(MvPolynomial.C MidpointRational.w*MvPolynomial.C tInv-1)*hh

def differential : Derivation ℤ G G :=
  Derivation.mk' deltaG.toIntLinearMap (fun a b => by
    change deltaG (a*b)=a*deltaG b+b*deltaG a
    rw [deltaG_mul]
    ring)

@[simp] theorem differential_apply (z : G) : differential z=deltaG z := rfl

@[simp] theorem deltaG_natCast (n : ℕ) : deltaG (n : G)=0 := by
  exact differential.map_natCast n

theorem deltaG_logistic_pow (z : G) (hz : deltaG z=imaginaryUnit*z*(z-1)) (n : ℕ) :
    deltaG (z^n)=imaginaryUnit*(n : G)*z^n*(z-1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, deltaG_mul, ih, hz, Nat.cast_add, Nat.cast_one]; ring

end JacobiShifted.SourceBridge
