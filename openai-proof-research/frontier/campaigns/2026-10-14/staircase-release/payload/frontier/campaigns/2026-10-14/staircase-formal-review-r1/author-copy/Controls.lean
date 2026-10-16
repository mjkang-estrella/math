/- Copyright (c) 2026 Myeongjin Kang. MIT. -/
import StaircaseSupport
import Mathlib.Data.ZMod.Basic

namespace StaircaseSupport.Controls

noncomputable section
open StaircaseSupport

abbrev C3 := Multiplicative (ZMod 3)
def c : C3 := Multiplicative.ofAdd 1

def z : C3 → ℤ := Pi.single 1 1
def theta : (C3 → ℤ) →ₗ[ℤ] ℤ := LinearMap.proj 1

/-- A genuine separating functional in the integral regular representation. -/
theorem regular_separates : Separates (regular (R := ℤ) (G := C3)) z theta := by
  intro g
  simp [theta, z, regular_apply, Pi.single_apply]

/-- Positive control: the constructed composite is the identity. -/
theorem positive_split :
    (coefficientMap (regular (R := ℤ) (G := C3)) theta).comp
      (orbitMap regular z) = LinearMap.id :=
  coefficientMap_comp_orbitMap regular z theta regular_separates

/-- Omitting the inverse in theta(g^-1 x) returns the wrong coordinate. -/
theorem wrong_inverse :
    theta (regular c (regular c z)) ≠ (Pi.single c (1 : ℤ) : C3 → ℤ) c := by
  have hci : c⁻¹ * c⁻¹ ≠ 1 := by decide
  norm_num [theta, regular_apply, z, Pi.single_apply, hci]

/-- Changing the sign of the orbit generator breaks the split identity. -/
theorem wrong_sign :
    coefficientMap (regular (R := ℤ) (G := C3)) theta (-z) ≠ Pi.single 1 1 := by
  intro h
  have h1 := congrFun h 1
  norm_num [coefficientMap_apply, theta, z, Pi.single_apply] at h1

/-- Positive shifts on coordinates disagree with the specified left regular action. -/
theorem wrong_action_orientation :
    (fun g => z (c * g)) ≠ regular c z := by
  intro h
  have hc := congrFun h c
  have hc2 : c * c ≠ 1 := by decide
  norm_num [regular_apply, z, Pi.single_apply, hc2] at hc

/-- A left inverse is not in general a right inverse. -/
theorem wrong_inverse_direction :
    let i : ℤ →ₗ[ℤ] ℤ × ℤ := LinearMap.inl ℤ ℤ ℤ
    let p : (ℤ × ℤ) →ₗ[ℤ] ℤ := LinearMap.fst ℤ ℤ ℤ
    p.comp i = LinearMap.id ∧ i.comp p ≠ LinearMap.id := by
  dsimp
  constructor
  · apply LinearMap.ext
    intro x
    rfl
  · intro h
    have h01 := LinearMap.congr_fun h (0, 1)
    have := congrArg Prod.snd h01
    norm_num at this

end
end StaircaseSupport.Controls

#print axioms StaircaseSupport.Controls.regular_separates
#print axioms StaircaseSupport.Controls.positive_split
#print axioms StaircaseSupport.Controls.wrong_inverse
#print axioms StaircaseSupport.Controls.wrong_sign
#print axioms StaircaseSupport.Controls.wrong_action_orientation
#print axioms StaircaseSupport.Controls.wrong_inverse_direction
