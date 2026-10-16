/- Copyright (c) 2026 Myeongjin Kang. MIT. Independent scoped review controls. -/
import StaircaseSupport
import Mathlib.Data.ZMod.Basic

open scoped BigOperators TensorProduct
namespace StaircaseReview
open StaircaseSupport
noncomputable section
attribute [local instance] Classical.propDecidable

-- The delta basis is translated by LEFT multiplication, including for nonabelian groups.
theorem delta_translation {R G : Type*} [CommRing R] [Group G] (h k : G) :
    regular (R := R) h (Pi.single k 1) = Pi.single (h * k) 1 := by
  classical
  ext g
  simp [regular_apply, Pi.single_apply, inv_mul_eq_iff_eq_mul]

-- Genuine proper summand in a nonfree ambient integral module, with S3 action.
abbrev S3 := Equiv.Perm (Fin 3)
abbrev Ambient := (S3 → ℤ) × ZMod 2

def rho : Representation ℤ S3 Ambient :=
  (regular (R := ℤ) (G := S3)).prod (Representation.trivial ℤ S3 (ZMod 2))
def z : Ambient := (Pi.single 1 1, 0)
def theta : Ambient →ₗ[ℤ] ℤ :=
  (LinearMap.proj 1).comp (LinearMap.fst ℤ (S3 → ℤ) (ZMod 2))

theorem separates : Separates rho z theta := by
  intro g
  simp [rho, z, theta, Representation.prod, Representation.trivial,
    regular_apply, Pi.single_apply]

theorem coefficient_is_fst (x : Ambient) : coefficientMap rho theta x = x.1 := by
  ext g
  simp [coefficientMap_apply, rho, theta, Representation.prod, regular_apply]

theorem orbit_is_inclusion (a : S3 → ℤ) : orbitMap rho z a = (a, 0) := by
  apply Prod.ext
  · have h := LinearMap.congr_fun (coefficientMap_comp_orbitMap rho z theta separates) a
    simpa only [LinearMap.comp_apply, LinearMap.id_apply, coefficient_is_fst] using h
  · change (LinearMap.snd ℤ (S3 → ℤ) (ZMod 2)) (orbitMap rho z a) = 0
    rw [orbitMap_apply, map_sum]
    simp [rho, z, Representation.prod, Representation.trivial]

theorem kernel_is_torsion (x : Ambient) :
    x ∈ LinearMap.ker (coefficientMap rho theta) ↔ x.1 = 0 := by
  simp [LinearMap.mem_ker, coefficient_is_fst]

theorem complement_nonzero :
    (0, (1 : ZMod 2)) ∈ LinearMap.ker (coefficientMap rho theta) ∧
    (0, (1 : ZMod 2)) ≠ (0 : Ambient) := by
  constructor
  · exact (kernel_is_torsion _).mpr rfl
  · intro h
    have := congrArg Prod.snd h
    norm_num at this

theorem proper_split :
    IsCompl (LinearMap.range (orbitMap rho z)) (LinearMap.ker (coefficientMap rho theta)) :=
  range_isCompl_ker rho z theta separates

-- C3 controls cannot distinguish left from right multiplication. S3 can.
def h : S3 := Equiv.swap 0 1
def k : S3 := Equiv.swap 1 2

theorem left_right_distinct : h * k ≠ k * h := by decide

theorem right_shift_fails :
    (Pi.single k (1 : ℤ) : S3 → ℤ) ((h * k) * h⁻¹) ≠
      regular h (Pi.single k 1) (h * k) := by
  have hc : (h * k) * h⁻¹ ≠ k := by decide
  simp [regular_apply, hc]

-- Arbitrary algebra, exact tensor types, and both intertwiners instantiated.
theorem extended_split (A : Type*) [CommRing A] [Algebra ℤ A] :
    ((coefficientMap rho theta).baseChange A).comp ((orbitMap rho z).baseChange A) =
      LinearMap.id :=
  baseChange_split _ _ (coefficientMap_comp_orbitMap rho z theta separates)

theorem extended_orbit_intertwines (A : Type*) [CommRing A] [Algebra ℤ A] (g : S3) :
    ((orbitMap rho z).baseChange A).comp ((regular g).baseChange A) =
      ((rho g).baseChange A).comp ((orbitMap rho z).baseChange A) := by
  apply baseChange_intertwines
  apply LinearMap.ext
  intro a
  exact orbitMap_equivariant rho z g a

theorem extended_coefficient_intertwines (A : Type*) [CommRing A] [Algebra ℤ A] (g : S3) :
    ((coefficientMap rho theta).baseChange A).comp ((rho g).baseChange A) =
      ((regular g).baseChange A).comp ((coefficientMap rho theta).baseChange A) := by
  apply baseChange_intertwines
  apply LinearMap.ext
  intro x
  exact coefficientMap_equivariant rho theta g x

theorem mod2_split :
    ((coefficientMap rho theta).baseChange (ZMod 2)).comp
      ((orbitMap rho z).baseChange (ZMod 2)) = LinearMap.id := extended_split (ZMod 2)

-- A general injection does fail after this same scalar extension.
def double : ℤ →ₗ[ℤ] ℤ := 2 • LinearMap.id

theorem double_injective : Function.Injective double := by
  intro x y he
  change (2 : ℤ) * x = 2 * y at he
  omega

theorem double_mod2_zero : double.baseChange (ZMod 2) = 0 := by
  ext
  change (1 : ZMod 2) ⊗ₜ[ℤ] (2 : ℤ) = 0
  have ht : (2 : ℤ) = 1 + 1 := rfl
  have ht2 : (1 : ZMod 2) + 1 = 0 := by decide
  rw [ht, TensorProduct.tmul_add, ← TensorProduct.add_tmul, ht2, TensorProduct.zero_tmul]

theorem tensor_one_nonzero : (1 : ZMod 2) ⊗ₜ[ℤ] (1 : ℤ) ≠ 0 := by
  intro he
  have hx := congrArg (TensorProduct.rid ℤ (ZMod 2)) he
  simp at hx

theorem double_mod2_not_injective : ¬ Function.Injective (double.baseChange (ZMod 2)) := by
  intro inj
  have he : double.baseChange (ZMod 2) ((1 : ZMod 2) ⊗ₜ[ℤ] (1 : ℤ)) =
      double.baseChange (ZMod 2) 0 := by rw [double_mod2_zero]; rfl
  exact tensor_one_nonzero (inj he)

-- Zero-ring instance: no Nontrivial hypothesis leaks into the interface.
theorem zero_ring_split :
    ((coefficientMap rho theta).baseChange (ZMod 1)).comp
      ((orbitMap rho z).baseChange (ZMod 1)) = LinearMap.id := extended_split (ZMod 1)

end
end StaircaseReview
