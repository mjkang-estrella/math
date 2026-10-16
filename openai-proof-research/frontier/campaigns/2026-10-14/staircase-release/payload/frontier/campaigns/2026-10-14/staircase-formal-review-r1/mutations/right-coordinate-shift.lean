/-
Copyright (c) 2026 Myeongjin Kang. Released under the MIT license.
Author: Myeongjin Kang (no affiliation).
-/
import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic

/-!
Supporting results only: the classical separating-functional regular-summand
construction and scalar extension. No staircase Specht module or palette
uniqueness is postulated or formalized here.
-/

open scoped BigOperators TensorProduct

namespace StaircaseSupport

noncomputable section Splitting

variable {R G M : Type*} [CommRing R] [Group G] [Fintype G]
  [AddCommGroup M] [Module R M]

attribute [local instance] Classical.propDecidable

/-- Regular coordinates: a basis vector at `g` is sent to the one at `h * g`.
Since `G` is finite, `G → R` is the finite free regular module. -/
def regular : Representation R G (G → R) where
  toFun h :=
    { toFun := fun a g => a (g * h⁻¹)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by
    apply LinearMap.ext
    intro a
    funext g
    simp
  map_mul' := by
    intro h k
    apply LinearMap.ext
    intro a
    funext g
    simp [mul_assoc]

omit [Fintype G] in
@[simp] theorem regular_apply (h : G) (a : G → R) (g : G) :
    regular h a g = a (g * h⁻¹) := rfl

/-- Orbit map, with no independence assumption. -/
def orbitMap (ρ : Representation R G M) (z : M) : (G → R) →ₗ[R] M where
  toFun a := ∑ g, a g • ρ g z
  map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by intros; simp [mul_smul, Finset.smul_sum]

/-- The explicit coefficient-functional retraction candidate. -/
def coefficientMap (ρ : Representation R G M) (θ : M →ₗ[R] R) : M →ₗ[R] (G → R) where
  toFun x g := θ (ρ g⁻¹ x)
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

@[simp] theorem orbitMap_apply (ρ : Representation R G M) (z : M) (a : G → R) :
    orbitMap ρ z a = ∑ g, a g • ρ g z := rfl

omit [Fintype G] in
@[simp] theorem coefficientMap_apply (ρ : Representation R G M) (θ : M →ₗ[R] R)
    (x : M) (g : G) : coefficientMap ρ θ x g = θ (ρ g⁻¹ x) := rfl

theorem orbitMap_equivariant (ρ : Representation R G M) (z : M) (h : G) (a : G → R) :
    orbitMap ρ z (regular h a) = ρ h (orbitMap ρ z a) := by
  classical
  simp only [orbitMap_apply, regular_apply, map_sum, map_smul]
  apply Fintype.sum_equiv (Equiv.mulLeft h⁻¹)
  intro g
  simp [← Module.End.mul_apply, ← map_mul]

omit [Fintype G] in
theorem coefficientMap_equivariant (ρ : Representation R G M) (θ : M →ₗ[R] R)
    (h : G) (x : M) : coefficientMap ρ θ (ρ h x) = regular h (coefficientMap ρ θ x) := by
  ext g
  simp [← Module.End.mul_apply, ← map_mul]

/-- This is the only representation-specific assumption for the splitting theorem.
It is NOT asserted for staircase Specht modules in this file. -/
def Separates (ρ : Representation R G M) (z : M) (θ : M →ₗ[R] R) : Prop :=
  ∀ g, θ (ρ g z) = if g = 1 then 1 else 0

omit [Fintype G] in
theorem coefficientMap_orbit (ρ : Representation R G M) (z : M) (θ : M →ₗ[R] R)
    (sep : Separates ρ z θ) (h : G) :
    coefficientMap ρ θ (ρ h z) = Pi.single h 1 := by
  classical
  unfold Separates at sep
  ext g
  simp [← Module.End.mul_apply, ← map_mul, sep, Pi.single_apply,
    inv_mul_eq_one, eq_comm]

/-- Explicit split identity over any commutative ring, including the zero ring. -/
theorem coefficientMap_comp_orbitMap (ρ : Representation R G M) (z : M)
    (θ : M →ₗ[R] R) (sep : Separates ρ z θ) :
    (coefficientMap ρ θ).comp (orbitMap ρ z) = LinearMap.id := by
  classical
  unfold Separates at sep
  apply LinearMap.ext
  intro a
  funext g
  simp only [LinearMap.comp_apply, orbitMap_apply, map_sum, map_smul]
  simp [coefficientMap_apply, ← Module.End.mul_apply, ← map_mul, sep, inv_mul_eq_one]

theorem orbitMap_injective (ρ : Representation R G M) (z : M) (θ : M →ₗ[R] R)
    (sep : Separates ρ z θ) : Function.Injective (orbitMap ρ z) := by
  have h := coefficientMap_comp_orbitMap ρ z θ sep
  exact Function.LeftInverse.injective (f := orbitMap ρ z)
    (g := coefficientMap ρ θ) (fun a => LinearMap.congr_fun h a)

/-- The explicit complementary component belongs to the kernel. -/
theorem complement_mem_ker (ρ : Representation R G M) (z : M) (θ : M →ₗ[R] R)
    (sep : Separates ρ z θ) (x : M) :
    x - orbitMap ρ z (coefficientMap ρ θ x) ∈ LinearMap.ker (coefficientMap ρ θ) := by
  have h := LinearMap.congr_fun (coefficientMap_comp_orbitMap ρ z θ sep)
    (coefficientMap ρ θ x)
  simp only [LinearMap.mem_ker, map_sub]
  exact sub_eq_zero.mpr h.symm

/-- Range and kernel are complementary as modules; both are also G-stable. -/
theorem range_isCompl_ker (ρ : Representation R G M) (z : M) (θ : M →ₗ[R] R)
    (sep : Separates ρ z θ) :
    IsCompl (LinearMap.range (orbitMap ρ z)) (LinearMap.ker (coefficientMap ρ θ)) := by
  constructor
  · rw [disjoint_iff]
    apply le_antisymm
    · intro x hx
      rcases hx.1 with ⟨a, rfl⟩
      have ha := LinearMap.congr_fun (coefficientMap_comp_orbitMap ρ z θ sep) a
      have hz : a = 0 := ha.symm.trans hx.2
      simp [hz]
    · exact bot_le
  · rw [codisjoint_iff]
    apply le_antisymm le_top
    intro x _
    exact Submodule.mem_sup.mpr ⟨orbitMap ρ z (coefficientMap ρ θ x),
      LinearMap.mem_range_self _ _, x - orbitMap ρ z (coefficientMap ρ θ x),
      complement_mem_ker ρ z θ sep x, add_sub_cancel _ _⟩

theorem range_stable (ρ : Representation R G M) (z : M) (h : G) (x : M)
    (hx : x ∈ LinearMap.range (orbitMap ρ z)) :
    ρ h x ∈ LinearMap.range (orbitMap ρ z) := by
  rcases hx with ⟨a, rfl⟩
  exact ⟨regular h a, orbitMap_equivariant ρ z h a⟩

omit [Fintype G] in
theorem ker_stable (ρ : Representation R G M) (θ : M →ₗ[R] R) (h : G) (x : M)
    (hx : x ∈ LinearMap.ker (coefficientMap ρ θ)) :
    ρ h x ∈ LinearMap.ker (coefficientMap ρ θ) := by
  rw [LinearMap.mem_ker] at hx ⊢
  rw [coefficientMap_equivariant, hx, map_zero]

end Splitting

section BaseChange

variable {R A V W : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- Scalar extension preserves a split identity without any flatness assumption. -/
theorem baseChange_split (i : V →ₗ[R] W) (p : W →ₗ[R] V)
    (split : p.comp i = LinearMap.id) :
    (p.baseChange A).comp (i.baseChange A) = LinearMap.id := by
  rw [← LinearMap.baseChange_comp, split, LinearMap.baseChange_id]

theorem baseChange_injective (i : V →ₗ[R] W) (p : W →ₗ[R] V)
    (split : p.comp i = LinearMap.id) : Function.Injective (i.baseChange A) :=
  Function.LeftInverse.injective (f := i.baseChange A) (g := p.baseChange A)
    (fun x => LinearMap.congr_fun (baseChange_split (A := A) i p split) x)

/-- Intertwining is preserved by scalar extension, as well as the split identity. -/
theorem baseChange_intertwines (f : V →ₗ[R] W) (u : V →ₗ[R] V)
    (v : W →ₗ[R] W) (equivariant : f.comp u = v.comp f) :
    (f.baseChange A).comp (u.baseChange A) =
      (v.baseChange A).comp (f.baseChange A) := by
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, equivariant]

end BaseChange

section IntegerSupport

/-- The support argument takes place in the integers, before any reduction of
coefficients. A zero sum of integer square deficits forces every deficit zero. -/
theorem integer_deficits_vanish {ι : Type*} (s : Finset ι) (d r : ι → ℤ)
    (budget : ∑ i ∈ s, (d i - r i)^2 = 0) :
    ∀ i ∈ s, d i = r i := by
  have each : ∀ i ∈ s, (d i - r i)^2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (d i - r i))).mp budget
  intro i hi
  have h := each i hi
  nlinarith [sq_nonneg (d i - r i)]

end IntegerSupport

end StaircaseSupport
