# Lean source appendix

Modules are in import order. Every block is byte-identical to src/.

### `Endpoint.lean`

```lean
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Parity

open scoped BigOperators
noncomputable section
namespace FiniteMT

def weight {d : ℕ} (s : Fin d → ℕ) : ℕ := ∑ i, s i

/-- The literal rational sum, represented modulo `p ^ k`.
    In the source range every denominator included by the filter is a unit. -/
def sumMod (p r k : ℕ) {d : ℕ} (s : Fin d → ℕ) : ZMod (p ^ k) :=
  ∑ x : Fin d → Fin (p ^ r),
    if (∀ i, 0 < (x i).val ∧ ¬ p ∣ (x i).val) ∧
        (∑ i, (x i).val) = p ^ r then
      ∏ i, (((x i).val : ZMod (p ^ k))⁻¹) ^ s i
    else 0

/-- All five conclusions of Wang--Zhao Conjecture 3.4. -/
def Conclusions (p r d : ℕ) (s : Fin d → ℕ) : Prop :=
  (d = 4 → Odd (weight s) →
    sumMod p r (2 * r - 1) s =
      (p : ZMod (p ^ (2 * r - 1))) ^ (2 * r - 2) * sumMod p 1 (2 * r - 1) s) ∧
  (d = 4 → Even (weight s) →
    sumMod p r r s = (p : ZMod (p ^ r)) ^ (r - 1) * sumMod p 1 r s) ∧
  (d = 5 → Even (weight s) →
    sumMod p r (2 * r - 1) s =
      (p : ZMod (p ^ (2 * r - 1))) ^ (2 * r - 2) * sumMod p 1 (2 * r - 1) s) ∧
  (2 ≤ r → Odd (d + weight s) → sumMod p r (2 * r - 2) s = 0) ∧
  (2 ≤ r → Even (d + weight s) → sumMod p r (r - 1) s = 0)

/-- Target proposition only. No proof of it is claimed by this file. -/
def SourceConjecture : Prop :=
  ∀ (p r d : ℕ) (s : Fin d → ℕ),
    p.Prime → 0 < r → 0 < d → (∀ i, 0 < s i) →
    weight s + 1 < p → Conclusions p r d s

#check SourceConjecture
#print axioms sumMod
#print axioms SourceConjecture
end FiniteMT
```

### `Carry.lean`

```lean
import Endpoint
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

open scoped BigOperators
noncomputable section
namespace FiniteMT

/-- Carry coordinates use positive natural b; the intended range is 1..d-1. -/
def carrySum (p r k : ℕ) {d : ℕ} (s : Fin d → ℕ) (b : ℕ) : ZMod (p^k) :=
  ∑ x : Fin d → Fin (p^r),
    if (∀ i, 0 < (x i).val ∧ ¬ p ∣ (x i).val) ∧
        (∑ i, (x i).val) = b*p^r then
      ∏ i, (((x i).val : ZMod (p^k))⁻¹)^s i else 0

theorem sumMod_eq_first (p r k : ℕ) {d : ℕ} (s : Fin d → ℕ) :
    sumMod p r k s = carrySum p r k s 1 := by
  simp only [sumMod, carrySum, one_mul]

/-- Addition form avoids an artificial fiber when ap < b. -/
def digitCondition (p a b : ℕ) {d : ℕ} (y : Fin d → Fin p) : Prop :=
  (∑ i, (y i).val) + b = a*p

instance (p a b : ℕ) {d : ℕ} (y : Fin d → Fin p) :
    Decidable (digitCondition p a b y) := Nat.decEq _ _

def carryCount (p d a b : ℕ) : ℕ :=
  ∑ y : Fin d → Fin p, if digitCondition p a b y then 1 else 0

def firstMoment (p d a b : ℕ) (i : Fin d) : ℕ :=
  ∑ y : Fin d → Fin p, if digitCondition p a b y then (y i).val else 0

def secondMoment (p d a b : ℕ) (i j : Fin d) : ℕ :=
  ∑ y : Fin d → Fin p,
    if digitCondition p a b y then (y i).val*(y j).val else 0

/-- Exact total first moment, before exploiting symmetry of the coordinates. -/
theorem firstMoment_total (p d a b : ℕ) :
    (∑ i, firstMoment p d a b i) = (a*p-b)*carryCount p d a b := by
  simp only [firstMoment, carryCount, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : digitCondition p a b y
  · simp only [hy, ite_true, mul_one]
    dsimp [digitCondition] at hy
    omega
  · simp only [hy, ite_false, Finset.sum_const_zero, mul_zero]

/-- Permuting coordinates preserves the carry fiber. -/
theorem digitCondition_perm (p a b : ℕ) {d : ℕ}
    (σ : Equiv.Perm (Fin d)) (y : Fin d → Fin p) :
    digitCondition p a b (fun i => y (σ i)) ↔ digitCondition p a b y := by
  have he : (∑ i, (y (σ i)).val) = ∑ i, (y i).val :=
    Equiv.sum_comp σ (fun i => (y i).val)
  simp only [digitCondition, he]

/-- The concrete finite-sum permutation used for moment symmetry. -/
def permuteDigits {p d : ℕ} (σ : Equiv.Perm (Fin d)) :
    (Fin d → Fin p) ≃ (Fin d → Fin p) where
  toFun y i := y (σ i)
  invFun y i := y (σ.symm i)
  left_inv y := by funext i; simp
  right_inv y := by funext i; simp

theorem firstMoment_symm (p d a b : ℕ) (i j : Fin d) :
    firstMoment p d a b i = firstMoment p d a b j := by
  classical
  let σ := Equiv.swap i j
  have he := Equiv.sum_comp (permuteDigits (p:=p) σ)
    (fun y : Fin d → Fin p => if digitCondition p a b y then (y i).val else 0)
  simp only [permuteDigits, Equiv.coe_fn_mk, digitCondition_perm] at he
  have hs : σ i = j := Equiv.swap_apply_left i j
  simpa only [hs, firstMoment] using he.symm

/-- Source proof equation (1), in division-free form. -/
theorem firstMoment_identity (p d a b : ℕ) (i : Fin d) :
    d*firstMoment p d a b i = (a*p-b)*carryCount p d a b := by
  calc
    _ = ∑ j : Fin d, firstMoment p d a b j := by
      simp_rw [firstMoment_symm p d a b _ i]
      simp
    _ = _ := firstMoment_total p d a b

/-- First-moment divisibility follows from the missing count divisibility. -/
theorem firstMoment_dvd_of_count (p d a b : ℕ) (i : Fin d)
    (hp : p.Prime) (hd : ¬ p ∣ d) (hc : p ∣ carryCount p d a b) :
    p ∣ firstMoment p d a b i := by
  have hm : p ∣ d * firstMoment p d a b i := by
    rw [firstMoment_identity]
    obtain ⟨q, hq⟩ := hc
    rw [hq]
    exact ⟨(a*p-b)*q, by ring⟩
  exact (hp.dvd_mul.mp hm).resolve_left hd

#print axioms firstMoment_dvd_of_count
#print axioms sumMod_eq_first
#print axioms firstMoment_identity
end FiniteMT
```

### `FourSum.lean`

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators
namespace FiniteMT

def fourEquiv (A : Type*) : (Fin 4 → A) ≃ A × A × A × A where
  toFun x := (x 0,x 1,x 2,x 3)
  invFun t := ![t.1,t.2.1,t.2.2.1,t.2.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv t := rfl

theorem fourEquiv_symm_apply (A : Type*) (t : A × A × A × A) :
    (fourEquiv A).symm t = ![t.1,t.2.1,t.2.2.1,t.2.2.2] := rfl

/-- An actual kernel-proved reindexing, used only to speed small literal tests. -/
theorem sum_four {A R : Type*} [Fintype A] [AddCommMonoid R]
    (f : (Fin 4 → A) → R) :
    (∑ x, f x) = ∑ a : A, ∑ b : A, ∑ c : A, ∑ d : A, f ![a,b,c,d] := by
  have h := (Equiv.sum_comp (fourEquiv A).symm f).symm
  simpa only [Fintype.sum_prod_type, fourEquiv_symm_apply] using h

#print axioms sum_four
end FiniteMT
```

### `Sanity.lean`

```lean
import Endpoint
import Mathlib.Data.Fin.VecNotation
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 10000
set_option maxHeartbeats 800000
open scoped BigOperators
namespace FiniteMT

/-- At depth one the coordinate bound alone makes the fiber empty. -/
theorem sumMod_depth_one (p r k : ℕ) (s : Fin 1 → ℕ) :
    sumMod p r k s = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro x _
  have hx : ¬ ((∀ i, 0 < (x i).val ∧ ¬ p ∣ (x i).val) ∧
      (∑ i, (x i).val) = p^r) := by
    intro h
    have hlt := (x 0).isLt
    have he : (x 0).val = p^r := by simpa using h.2
    omega
  simp only [ite_eq_right_iff.mpr (fun h => (hx h).elim)]

theorem sanity_weight13 : weight ![8,1,1,1] = 11 := by decide

theorem sanity_nonempty : sumMod 3 1 1 ![1,1] = (1 : ZMod 3) := by
  decide +kernel

theorem sanity_scaling : sumMod 3 2 1 ![1,1] = (0 : ZMod 3) := by
  decide +kernel

#print axioms sumMod_depth_one
#print axioms sanity_weight13
#print axioms sanity_nonempty
#print axioms sanity_scaling
end FiniteMT
```

### `Taylor.lean`

```lean
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace FiniteMT.Taylor
variable {R : Type*} [CommRing R]

/-- The exact second jet multiplication law when `h³=0`. -/
theorem jet_mul (h a b c d : R) (hh : h^3 = 0) :
    (1+h*a+h^2*b)*(1+h*c+h^2*d) =
      1+h*(a+c)+h^2*(b+d+a*c) := by
  have h4 : h^4 = 0 := by rw [show 4 = 3+1 from rfl, pow_add, hh, zero_mul]
  linear_combination (a*d+b*c)*hh + (b*d)*h4

/-- Inverse of a unit after a nilpotent additive perturbation. -/
def perturb (u : Rˣ) (h y : R) (hh : h^3 = 0) : Rˣ :=
  { val := (u:R)+h*y
    inv := (↑u⁻¹:R)*(1-h*(y*(↑u⁻¹:R))+h^2*(y*(↑u⁻¹:R))^2)
    val_inv := by
      have hu : (u:R)*(↑u⁻¹:R) = 1 := u.val_inv
      have he : ((u:R)+h*y)*((↑u⁻¹:R)*
          (1-h*(y*(↑u⁻¹:R))+h^2*(y*(↑u⁻¹:R))^2)) =
          1+h^3*y^3*(↑u⁻¹:R)^3 := by
        calc
          _ = ((u:R)*(↑u⁻¹:R))*(1-h*y*(↑u⁻¹:R)+h^2*y^2*(↑u⁻¹:R)^2) +
              h*y*(↑u⁻¹:R)-h^2*y^2*(↑u⁻¹:R)^2+h^3*y^3*(↑u⁻¹:R)^3 := by ring
          _ = _ := by rw [hu]; ring
      rw [he, hh]; ring
    inv_val := by
      rw [mul_comm]
      have hu : (u:R)*(↑u⁻¹:R) = 1 := u.val_inv
      calc
        _ = ((u:R)*(↑u⁻¹:R))*(1-h*y*(↑u⁻¹:R)+h^2*y^2*(↑u⁻¹:R)^2) +
            h*y*(↑u⁻¹:R)-h^2*y^2*(↑u⁻¹:R)^2+h^3*y^3*(↑u⁻¹:R)^3 := by ring
        _ = 1 := by rw [hu, hh]; ring }

theorem perturb_val (u : Rˣ) (h y : R) (hh : h^3 = 0) :
    (perturb u h y hh : R) = (u:R)+h*y := rfl

theorem inverse_perturb (u : Rˣ) (h y : R) (hh : h^3 = 0) :
    (↑(perturb u h y hh)⁻¹ : R) =
      (↑u⁻¹:R)*(1-h*(y*(↑u⁻¹:R))+h^2*(y*(↑u⁻¹:R))^2) := rfl

/-- Uniform in the exponent, including zero. No division by 2. -/
theorem inverse_pow_perturb (u : Rˣ) (h y : R) (hh : h^3 = 0) (n : ℕ) :
    (↑(perturb u h y hh)⁻¹ : R)^n =
      (↑u⁻¹:R)^n * (1-h*(n:R)*(y*(↑u⁻¹:R)) +
        h^2*((n+1).choose 2:R)*(y*(↑u⁻¹:R))^2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, inverse_perturb, pow_succ]
    have hc : ((n+1+1).choose 2:R) = (n+1:R) + ((n+1).choose 2:R) := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add]
      simp
    rw [hc]
    have hj := jet_mul h (-(n:R)*(y*(↑u⁻¹:R)))
      (((n+1).choose 2:R)*(y*(↑u⁻¹:R))^2) (-(y*(↑u⁻¹:R)))
      ((y*(↑u⁻¹:R))^2) hh
    calc
      _ = (↑u⁻¹:R)^n*(↑u⁻¹:R) *
          ((1+h*(-(n:R)*(y*(↑u⁻¹:R)))+h^2*(((n+1).choose 2:R)*(y*(↑u⁻¹:R))^2))*
           (1+h*(-(y*(↑u⁻¹:R)))+h^2*((y*(↑u⁻¹:R))^2))) := by ring
      _ = _ := by rw [hj]; push_cast; ring

/-- Coefficients of a product of second jets. -/
def linear : List (R × R) → R
  | [] => 0
  | c :: cs => c.1 + linear cs

def quadratic : List (R × R) → R
  | [] => 0
  | c :: cs => c.2 + quadratic cs + c.1 * linear cs

def jetProduct (h : R) (cs : List (R × R)) : R :=
  (cs.map fun c => 1+h*c.1+h^2*c.2).prod

theorem product_jets (h : R) (hh : h^3=0) (cs : List (R × R)) :
    jetProduct h cs = 1+h*linear cs+h^2*quadratic cs := by
  induction cs with
  | nil => simp [jetProduct, linear, quadratic]
  | cons c cs ih =>
    simp only [jetProduct, List.map_cons, List.prod_cons] at *
    rw [ih, jet_mul h c.1 c.2 (linear cs) (quadratic cs) hh]
    rfl

/-- A coordinate contains its low unit, upper digit and exponent. -/
abbrev Coordinate (R : Type*) [CommRing R] := Rˣ × R × ℕ

def coeff (c : Coordinate R) : R × R :=
  (-(c.2.2:R)*(c.2.1*(↑c.1⁻¹:R)),
   ((c.2.2+1).choose 2:R)*(c.2.1*(↑c.1⁻¹:R))^2)

def baseProduct (cs : List (Coordinate R)) : R :=
  (cs.map fun (c : Coordinate R) => (↑c.1⁻¹:R)^c.2.2).prod

def liftedProduct (h : R) (hh : h^3=0) (cs : List (Coordinate R)) : R :=
  (cs.map fun (c : Coordinate R) => (↑(perturb c.1 h c.2.1 hh)⁻¹:R)^c.2.2).prod

/-- The second-order Taylor expansion, uniform in depth and every exponent. -/
theorem product_inverse_perturb (h : R) (hh : h^3=0) (cs : List (Coordinate R)) :
    liftedProduct h hh cs = baseProduct cs *
      (1+h*linear (cs.map coeff)+h^2*quadratic (cs.map coeff)) := by
  have hf : liftedProduct h hh cs = baseProduct cs * jetProduct h (cs.map coeff) := by
    induction cs with
    | nil => simp [liftedProduct, baseProduct, jetProduct]
    | cons c cs ih =>
      simp only [liftedProduct, baseProduct, List.map_cons, List.prod_cons,
        jetProduct] at *
      rw [inverse_pow_perturb, ih]
      simp only [coeff]
      ring
  rw [hf, product_jets h hh]

#print axioms inverse_pow_perturb
#print axioms product_inverse_perturb
end FiniteMT.Taylor
```

### `TaylorSum.lean`

```lean
import Taylor
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card

open scoped BigOperators
namespace FiniteMT.Taylor
variable {R Y : Type*} [CommRing R] [Fintype Y]

/-- A family of first and second coefficients, one pair per coordinate. -/
def evaluate (cs : List ((Y → R) × (Y → R))) (y : Y) : List (R × R) :=
  cs.map fun c => (c.1 y, c.2 y)

theorem scaled_cross_zero (h : R) (a : Y → R)
    (cs : List ((Y → R) × (Y → R)))
    (ha : ∀ c ∈ cs, h^2 * (∑ y, a y * c.1 y) = 0) :
    h^2 * (∑ y, a y * linear (evaluate cs y)) = 0 := by
  induction cs with
  | nil => simp [evaluate, linear]
  | cons c cs ih =>
    simp only [evaluate, List.map_cons, linear, mul_add, Finset.sum_add_distrib]
    rw [ha c (by simp)]
    have hz : h^2 * (∑ y, a y * linear (evaluate cs y)) = 0 :=
      ih (fun e he => ha e (by simp [he]))
    simpa only [zero_add, evaluate] using hz

/-- Exactly the moment annihilation needed at double precision. -/
theorem scaled_quadratic_zero (h : R)
    (cs : List ((Y → R) × (Y → R)))
    (hb : ∀ c ∈ cs, h^2 * (∑ y, c.2 y) = 0)
    (hab : ∀ c ∈ cs, ∀ e ∈ cs, h^2 * (∑ y, c.1 y * e.1 y) = 0) :
    h^2 * (∑ y, quadratic (evaluate cs y)) = 0 := by
  induction cs with
  | nil => simp [evaluate, quadratic]
  | cons c cs ih =>
    simp only [evaluate, List.map_cons, quadratic, Finset.sum_add_distrib, mul_add]
    rw [hb c (by simp)]
    have htail : h^2 * (∑ y, quadratic (evaluate cs y)) = 0 :=
      ih (fun e he => hb e (by simp [he]))
        (fun e he f hf => hab e (by simp [he]) f (by simp [hf]))
    have hcross := scaled_cross_zero h c.1 cs
      (fun e he => hab c (by simp) e (by simp [he]))
    change 0 + h^2 * (∑ y, quadratic (evaluate cs y)) +
      h^2 * (∑ y, c.1 y * linear (evaluate cs y)) = 0
    rw [htail, hcross, add_zero, add_zero]

/-- Summing the uniform product expansion and eliminating all quadratic terms.
The moment hypotheses are multiplied by `h²`, so in a modular application
only one extra p in the carry moments is needed. -/
theorem sum_product_jets (h : R) (hh : h^3=0)
    (cs : List ((Y → R) × (Y → R)))
    (hb : ∀ c ∈ cs, h^2 * (∑ y, c.2 y) = 0)
    (hab : ∀ c ∈ cs, ∀ e ∈ cs, h^2 * (∑ y, c.1 y * e.1 y) = 0) :
    (∑ y, jetProduct h (evaluate cs y)) =
      (Fintype.card Y:R) + h * ∑ y, linear (evaluate cs y) := by
  simp_rw [product_jets h hh]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, scaled_quadratic_zero h cs hb hab]
  simp

/-- Unit and exponent fixed along a digit fiber, with varying upper digit. -/
abbrev FamilyCoordinate (R Y : Type*) [CommRing R] := Rˣ × (Y → R) × ℕ

def atDigit (y : Y) (c : FamilyCoordinate R Y) : Coordinate R :=
  (c.1, c.2.1 y, c.2.2)

def familyCoeff (c : FamilyCoordinate R Y) : (Y → R) × (Y → R) :=
  (fun y => (coeff (atDigit y c)).1, fun y => (coeff (atDigit y c)).2)

omit [Fintype Y] in
theorem family_evaluate (cs : List (FamilyCoordinate R Y)) (y : Y) :
    evaluate (cs.map familyCoeff) y = (cs.map (atDigit y)).map coeff := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [evaluate, List.map_cons] at *; rw [← ih]; rfl

/-- Uniform second-order expansion of the lifted sum on one digit fiber.
This is conditional only on moment cancellation, not on Taylor expansion. -/
theorem sum_product_inverse_perturb (h : R) (hh : h^3=0)
    (cs : List (FamilyCoordinate R Y))
    (hb : ∀ c ∈ cs.map familyCoeff, h^2 * (∑ y, c.2 y) = 0)
    (hab : ∀ c ∈ cs.map familyCoeff, ∀ e ∈ cs.map familyCoeff,
      h^2 * (∑ y, c.1 y * e.1 y) = 0) :
    (∑ y, liftedProduct h hh (cs.map (atDigit y))) =
      (cs.map fun (c : FamilyCoordinate R Y) => (↑c.1⁻¹:R)^c.2.2).prod *
        ((Fintype.card Y:R) + h * ∑ y, linear (evaluate (cs.map familyCoeff) y)) := by
  have hbase (y : Y) : baseProduct (cs.map (atDigit y)) =
      (cs.map fun (c : FamilyCoordinate R Y) => (↑c.1⁻¹:R)^c.2.2).prod := by
    simp [baseProduct, List.map_map, Function.comp_def, atDigit]
  simp_rw [product_inverse_perturb h hh, hbase, ← family_evaluate]
  rw [← Finset.mul_sum]
  congr 1
  simpa only [product_jets h hh] using sum_product_jets h hh (cs.map familyCoeff) hb hab

#print axioms scaled_quadratic_zero
#print axioms sum_product_inverse_perturb
end FiniteMT.Taylor
```

### `ModularTaylor.lean`

```lean
import TaylorSum
import Mathlib.Data.ZMod.Basic
import Lean.Elab.Tactic.Omega

import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators
namespace FiniteMT.Taylor

/-- The critical precision inequality, including the boundary r=1. -/
theorem power_cube_zero (p r : ℕ) (hr : 1 ≤ r) :
    ((p : ZMod (p^(2*r+1)))^r)^3 = 0 := by
  rw [← pow_mul]
  exact ZMod.natCast_pow_eq_zero_of_le p (by omega)

/-- One p in a moment is sufficient after multiplying by the quadratic scale. -/
theorem quadratic_moment_zero (p r : ℕ)
    (m : ZMod (p^(2*r+1))) (hm : (p : ZMod (p^(2*r+1))) ∣ m) :
    ((p : ZMod (p^(2*r+1)))^r)^2 * m = 0 := by
  obtain ⟨q, rfl⟩ := hm
  rw [← pow_mul]
  calc
    _ = (p : ZMod (p^(2*r+1)))^(2*r+1) * q := by ring
    _ = 0 := by rw [ZMod.natCast_pow_eq_zero_of_le p (by omega), zero_mul]

/-- The prototype uses the actual `ZMod` inverse, not a replacement inverse. -/
theorem inverse_pow_lift (m : ℕ) (u : (ZMod m)ˣ) (h y : ZMod m)
    (hh : h^3=0) (n : ℕ) :
    (((u:ZMod m)+h*y)⁻¹)^n = (↑u⁻¹:ZMod m)^n *
      (1-h*(n:ZMod m)*(y*(↑u⁻¹:ZMod m)) +
       h^2*((n+1).choose 2:ZMod m)*(y*(↑u⁻¹:ZMod m))^2) := by
  have hv := inverse_pow_perturb u h y hh n
  rw [← ZMod.inv_coe_unit, perturb_val] at hv
  exact hv

/-- Natural coordinates permitted by the source filter are units at every
positive precision. -/
theorem coordinate_isUnit (p k x : ℕ) (hp : p.Prime) (hk : 0 < k)
    (hx : ¬ p ∣ x) : IsUnit (x : ZMod (p^k)) :=
  (ZMod.isUnit_natCast_iff_not_dvd_pow hp hk).mpr hx

/-- Finite-depth form of the pointwise expansion, uniform in all exponents. -/
theorem finite_product_inverse_lift (m d : ℕ) (u : Fin d → (ZMod m)ˣ)
    (h : ZMod m) (y : Fin d → ZMod m) (s : Fin d → ℕ) (hh : h^3=0) :
    (∏ i, (((u i:ZMod m)+h*y i)⁻¹)^s i) =
      (∏ i, (↑(u i)⁻¹:ZMod m)^s i) *
        (1+h*linear (List.ofFn fun i => coeff (u i,y i,s i)) +
         h^2*quadratic (List.ofFn fun i => coeff (u i,y i,s i))) := by
  have hv := product_inverse_perturb h hh (List.ofFn fun i => (u i,y i,s i))
  simp only [liftedProduct, baseProduct, List.map_ofFn, List.prod_ofFn] at hv
  simp_rw [← ZMod.inv_coe_unit, perturb_val] at hv
  simpa only [Function.comp_def, ZMod.inv_coe_unit] using hv

#print axioms inverse_pow_lift
#print axioms finite_product_inverse_lift
#print axioms coordinate_isUnit
#print axioms power_cube_zero
#print axioms quadratic_moment_zero
end FiniteMT.Taylor
```

### `TaylorMoments.lean`

```lean
import ModularTaylor

open scoped BigOperators
namespace FiniteMT.Taylor
variable {R Y : Type*} [CommRing R] [Fintype Y]

def firstConstant (c : FamilyCoordinate R Y) : R := -(c.2.2:R)*(↑c.1⁻¹:R)
def secondConstant (c : FamilyCoordinate R Y) : R :=
  ((c.2.2+1).choose 2:R)*(↑c.1⁻¹:R)^2

omit [Fintype Y] in
theorem familyCoeff_first (c : FamilyCoordinate R Y) (y : Y) :
    (familyCoeff c).1 y = firstConstant c * c.2.1 y := by
  dsimp [familyCoeff, coeff, atDigit, firstConstant]
  ring

omit [Fintype Y] in
theorem familyCoeff_second (c : FamilyCoordinate R Y) (y : Y) :
    (familyCoeff c).2 y = secondConstant c * (c.2.1 y)^2 := by
  dsimp [familyCoeff, coeff, atDigit, secondConstant]
  ring

theorem scaled_const_moment_zero (h C : R) (f : Y → R)
    (hf : h^2 * (∑ y, f y) = 0) : h^2 * (∑ y, C*f y) = 0 := by
  rw [← Finset.mul_sum]
  calc
    _ = C*(h^2 * ∑ y, f y) := by ring
    _ = 0 := by rw [hf, mul_zero]

theorem scaled_mixed_moment_zero (h C D : R) (f g : Y → R)
    (hf : h^2 * (∑ y, f y*g y) = 0) :
    h^2 * (∑ y, (C*f y)*(D*g y)) = 0 := by
  have he (y : Y) : (C*f y)*(D*g y) = (C*D)*(f y*g y) := by ring
  simp_rw [he]
  exact scaled_const_moment_zero h (C*D) (fun y => f y*g y) hf

/-- The uniform lifted-sum expansion with hypotheses on the RAW digit moments.
No bound on depth or exponents is imposed. The concrete digit-fiber moment
vanishing and its bijection with the source sum are still separate obligations. -/
theorem sum_inverse_of_digit_moments (h : R) (hh : h^3=0)
    (cs : List (FamilyCoordinate R Y))
    (hsq : ∀ c ∈ cs, h^2 * (∑ y, (c.2.1 y)^2) = 0)
    (hmix : ∀ c ∈ cs, ∀ e ∈ cs, h^2 * (∑ y, c.2.1 y*e.2.1 y) = 0) :
    (∑ y, liftedProduct h hh (cs.map (atDigit y))) =
      (cs.map fun (c : FamilyCoordinate R Y) => (↑c.1⁻¹:R)^c.2.2).prod *
        ((Fintype.card Y:R) + h * ∑ y, linear (evaluate (cs.map familyCoeff) y)) := by
  apply sum_product_inverse_perturb h hh cs
  · intro c hc
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
    simp_rw [familyCoeff_second]
    exact scaled_const_moment_zero h (secondConstant e) (fun y => (e.2.1 y)^2) (hsq e he)
  · intro c hc e he
    obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    simp_rw [familyCoeff_first]
    exact scaled_mixed_moment_zero h (firstConstant c') (firstConstant e')
      c'.2.1 e'.2.1 (hmix c' hc' e' he')

#print axioms sum_inverse_of_digit_moments
end FiniteMT.Taylor
```

### `UniformLift.lean`

```lean
import TaylorMoments

open scoped BigOperators
namespace FiniteMT.Taylor

/-- The exact uniform digit-fiber Taylor step in the final ambient ring.
Depth and exponents are arbitrary. The only residual hypotheses are the
concrete raw second-moment divisibilities for the chosen finite digit fiber.
The literal source fiber equivalence has NOT been assumed or proved here. -/
theorem modular_lifted_sum {Y : Type*} [Fintype Y] (p r d : ℕ) (hr : 1 ≤ r)
    (u : Fin d → (ZMod (p^(2*r+1)))ˣ) (s : Fin d → ℕ)
    (digits : Fin d → Y → ZMod (p^(2*r+1)))
    (hm : ∀ i j, (p : ZMod (p^(2*r+1))) ∣ ∑ y, digits i y*digits j y) :
    let h : ZMod (p^(2*r+1)) := (p : ZMod (p^(2*r+1)))^r
    let cs : List (FamilyCoordinate (ZMod (p^(2*r+1))) Y) :=
      List.ofFn fun i => (u i,digits i,s i)
    (∑ y, ∏ i, (((u i : ZMod (p^(2*r+1)))+h*digits i y)⁻¹)^s i) =
      (∏ i, (↑(u i)⁻¹ : ZMod (p^(2*r+1)))^s i) *
        ((Fintype.card Y : ZMod (p^(2*r+1))) +
          h * ∑ y, linear (evaluate (cs.map familyCoeff) y)) := by
  intro h cs
  have hsq : ∀ c ∈ cs, h^2 * (∑ y, (c.2.1 y)^2) = 0 := by
    intro c hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    exact quadratic_moment_zero p r _ (by simpa only [pow_two] using hm i i)
  have hmix : ∀ c ∈ cs, ∀ e ∈ cs, h^2 * (∑ y, c.2.1 y*e.2.1 y) = 0 := by
    intro c hc e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp he
    exact quadratic_moment_zero p r _ (hm i j)
  have hv := sum_inverse_of_digit_moments h (power_cube_zero p r hr) cs hsq hmix
  simp only [cs, liftedProduct, List.map_ofFn, List.prod_ofFn, Function.comp_def,
    atDigit] at hv
  simp_rw [← ZMod.inv_coe_unit, perturb_val] at hv
  simpa only [cs, List.map_ofFn, List.prod_ofFn, Function.comp_def,
    ZMod.inv_coe_unit] using hv

#print axioms modular_lifted_sum
end FiniteMT.Taylor
```

### `WeakInduction.lean`

```lean
import Carry
import Sanity
import Mathlib.RingTheory.Ideal.Basic

open scoped BigOperators
namespace FiniteMT

/-- An explicitly UNPROVED input of the remaining carry argument.
It is weaker than the double-precision recurrence: only p^r is retained. -/
def WeakCarryRecurrence (p d k : ℕ) : Prop :=
  ∀ (r : ℕ), 1 ≤ r → ∀ (s : Fin d → ℕ) (a : ℕ), 1 ≤ a → a < d →
    (p : ZMod (p^k))^r ∣
      carrySum p (r+1) k s a -
        ∑ b : Fin (d-1), (carryCount p d a (b.val+1) : ZMod (p^k)) *
          carrySum p r k s (b.val+1)

/-- Precise missing zeroth-moment input. -/
def CountDivisibility (p d : ℕ) : Prop :=
  ∀ (a b : ℕ), 1 ≤ a → a < d → 1 ≤ b → b < d → p ∣ carryCount p d a b

/-- Complete induction, conditional on the two concrete missing inputs. -/
theorem weak_divisibility_of_carry (p d k : ℕ)
    (hc : CountDivisibility p d) (hl : WeakCarryRecurrence p d k) :
    ∀ r, 1 ≤ r → ∀ (s : Fin d → ℕ) a, 1 ≤ a → a < d →
      (p : ZMod (p^k))^(r-1) ∣ carrySum p r k s a := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base => simp
  | succ r hr ih =>
    intro s a ha had
    have hpow : (p : ZMod (p^k))^r =
        (p : ZMod (p^k))*(p : ZMod (p^k))^(r-1) := by
      rw [← pow_succ']; congr 1; omega
    have hsum : (p : ZMod (p^k))^r ∣
        ∑ b : Fin (d-1), (carryCount p d a (b.val+1) : ZMod (p^k)) *
          carrySum p r k s (b.val+1) := by
      apply Finset.dvd_sum
      intro b _
      have hb : b.val+1 < d := by have := b.isLt; omega
      have hM : (p : ZMod (p^k)) ∣ (carryCount p d a (b.val+1) : ZMod (p^k)) := by
        obtain ⟨q, hq⟩ := hc a (b.val+1) ha had (by omega) hb
        refine ⟨(q : ZMod (p^k)), ?_⟩
        rw [hq, Nat.cast_mul]
      rw [hpow]
      exact mul_dvd_mul hM (ih s (b.val+1) (by omega) hb)
    have hz := dvd_add (hl r hr s a ha had) hsum
    simpa only [sub_add_cancel, Nat.add_sub_cancel] using hz

/-- Literal source clause (16), STILL CONDITIONAL on concrete carry inputs.
There is deliberately no unconditional theorem named assertion16. -/
theorem assertion16_of_carry (p r d : ℕ) (s : Fin d → ℕ) (hr : 2 ≤ r)
    (hd : 0 < d) (hc : CountDivisibility p d)
    (hl : WeakCarryRecurrence p d (r-1)) :
    sumMod p r (r-1) s = 0 := by
  by_cases hd1 : d = 1
  · subst d
    exact sumMod_depth_one p r (r-1) s
  · have hdiv := weak_divisibility_of_carry p d (r-1) hc hl r (by omega) s 1
      (by omega) (by omega)
    rw [← sumMod_eq_first] at hdiv
    have hz : (p : ZMod (p^(r-1)))^(r-1) = 0 :=
      ZMod.natCast_pow_eq_zero_of_le p (by omega)
    rw [hz] at hdiv
    exact zero_dvd_iff.mp hdiv

#print axioms weak_divisibility_of_carry
#print axioms assertion16_of_carry
end FiniteMT
```

### `Obligations.lean`

```lean
import WeakInduction

namespace FiniteMT

/-- These six propositions are explicit residual inputs, not theorems. -/
def Scaling12 : Prop := ∀ (p r : ℕ) (s : Fin 4 → ℕ),
  p.Prime → 0 < r → (∀ i, 0 < s i) → weight s+1 < p → Odd (weight s) →
  sumMod p r (2*r-1) s = (p : ZMod (p^(2*r-1)))^(2*r-2)*sumMod p 1 (2*r-1) s

def Scaling13 : Prop := ∀ (p r : ℕ) (s : Fin 4 → ℕ),
  p.Prime → 0 < r → (∀ i, 0 < s i) → weight s+1 < p → Even (weight s) →
  sumMod p r r s = (p : ZMod (p^r))^(r-1)*sumMod p 1 r s

def Scaling14 : Prop := ∀ (p r : ℕ) (s : Fin 5 → ℕ),
  p.Prime → 0 < r → (∀ i, 0 < s i) → weight s+1 < p → Even (weight s) →
  sumMod p r (2*r-1) s = (p : ZMod (p^(2*r-1)))^(2*r-2)*sumMod p 1 (2*r-1) s

def Divisibility15 : Prop := ∀ (p r d : ℕ) (s : Fin d → ℕ),
  p.Prime → 2 ≤ r → 0 < d → (∀ i, 0 < s i) → weight s+1 < p →
  Odd (d+weight s) → sumMod p r (2*r-2) s = 0

def CountTheorem : Prop := ∀ p d, p.Prime → d+1 < p → CountDivisibility p d

def WeakLiftTheorem : Prop := ∀ p d k, p.Prime → d+1 < p → WeakCarryRecurrence p d k

theorem depth_le_weight {d : ℕ} (s : Fin d → ℕ) (hs : ∀ i, 0 < s i) :
    d ≤ weight s := by
  calc
    d = ∑ _i : Fin d, 1 := by simp
    _ ≤ weight s := Finset.sum_le_sum (fun i _ => hs i)

/-- Exact assembly certificate. Every substantive unproved input is visible.
In particular this theorem is NOT a proof of `SourceConjecture`. -/
theorem source_of_obligations (h12 : Scaling12) (h13 : Scaling13) (h14 : Scaling14)
    (h15 : Divisibility15) (hc : CountTheorem) (hl : WeakLiftTheorem) :
    SourceConjecture := by
  intro p r d s hp hr hd hs hw
  have hdp : d+1 < p := lt_of_le_of_lt (Nat.add_le_add_right (depth_le_weight s hs) 1) hw
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hd4 ho
    subst d
    exact h12 p r s hp hr hs hw ho
  · intro hd4 he
    subst d
    exact h13 p r s hp hr hs hw he
  · intro hd5 he
    subst d
    exact h14 p r s hp hr hs hw he
  · intro hr2 ho
    exact h15 p r d s hp hr2 hd hs hw ho
  · intro hr2 _
    exact assertion16_of_carry p r d s hr2 hd (hc p d hp hdp) (hl p d (r-1) hp hdp)

#print axioms depth_le_weight
#print axioms source_of_obligations
end FiniteMT
```

### `Inventory.lean`

```lean
import Endpoint
import Sanity
import FourSum
import Taylor
import TaylorSum
import ModularTaylor
import TaylorMoments
import UniformLift
import Carry
import WeakInduction
import Obligations

#check FiniteMT.sumMod_depth_one
#print axioms FiniteMT.sumMod_depth_one
#check FiniteMT.sanity_weight13
#print axioms FiniteMT.sanity_weight13
#check FiniteMT.sanity_nonempty
#print axioms FiniteMT.sanity_nonempty
#check FiniteMT.sanity_scaling
#print axioms FiniteMT.sanity_scaling
#check FiniteMT.fourEquiv_symm_apply
#print axioms FiniteMT.fourEquiv_symm_apply
#check FiniteMT.sum_four
#print axioms FiniteMT.sum_four
#check FiniteMT.Taylor.jet_mul
#print axioms FiniteMT.Taylor.jet_mul
#check FiniteMT.Taylor.perturb_val
#print axioms FiniteMT.Taylor.perturb_val
#check FiniteMT.Taylor.inverse_perturb
#print axioms FiniteMT.Taylor.inverse_perturb
#check FiniteMT.Taylor.inverse_pow_perturb
#print axioms FiniteMT.Taylor.inverse_pow_perturb
#check FiniteMT.Taylor.product_jets
#print axioms FiniteMT.Taylor.product_jets
#check FiniteMT.Taylor.product_inverse_perturb
#print axioms FiniteMT.Taylor.product_inverse_perturb
#check FiniteMT.Taylor.scaled_cross_zero
#print axioms FiniteMT.Taylor.scaled_cross_zero
#check FiniteMT.Taylor.scaled_quadratic_zero
#print axioms FiniteMT.Taylor.scaled_quadratic_zero
#check FiniteMT.Taylor.sum_product_jets
#print axioms FiniteMT.Taylor.sum_product_jets
#check FiniteMT.Taylor.family_evaluate
#print axioms FiniteMT.Taylor.family_evaluate
#check FiniteMT.Taylor.sum_product_inverse_perturb
#print axioms FiniteMT.Taylor.sum_product_inverse_perturb
#check FiniteMT.Taylor.power_cube_zero
#print axioms FiniteMT.Taylor.power_cube_zero
#check FiniteMT.Taylor.quadratic_moment_zero
#print axioms FiniteMT.Taylor.quadratic_moment_zero
#check FiniteMT.Taylor.inverse_pow_lift
#print axioms FiniteMT.Taylor.inverse_pow_lift
#check FiniteMT.Taylor.coordinate_isUnit
#print axioms FiniteMT.Taylor.coordinate_isUnit
#check FiniteMT.Taylor.finite_product_inverse_lift
#print axioms FiniteMT.Taylor.finite_product_inverse_lift
#check FiniteMT.Taylor.familyCoeff_first
#print axioms FiniteMT.Taylor.familyCoeff_first
#check FiniteMT.Taylor.familyCoeff_second
#print axioms FiniteMT.Taylor.familyCoeff_second
#check FiniteMT.Taylor.scaled_const_moment_zero
#print axioms FiniteMT.Taylor.scaled_const_moment_zero
#check FiniteMT.Taylor.scaled_mixed_moment_zero
#print axioms FiniteMT.Taylor.scaled_mixed_moment_zero
#check FiniteMT.Taylor.sum_inverse_of_digit_moments
#print axioms FiniteMT.Taylor.sum_inverse_of_digit_moments
#check FiniteMT.Taylor.modular_lifted_sum
#print axioms FiniteMT.Taylor.modular_lifted_sum
#check FiniteMT.sumMod_eq_first
#print axioms FiniteMT.sumMod_eq_first
#check FiniteMT.firstMoment_total
#print axioms FiniteMT.firstMoment_total
#check FiniteMT.digitCondition_perm
#print axioms FiniteMT.digitCondition_perm
#check FiniteMT.firstMoment_symm
#print axioms FiniteMT.firstMoment_symm
#check FiniteMT.firstMoment_identity
#print axioms FiniteMT.firstMoment_identity
#check FiniteMT.firstMoment_dvd_of_count
#print axioms FiniteMT.firstMoment_dvd_of_count
#check FiniteMT.weak_divisibility_of_carry
#print axioms FiniteMT.weak_divisibility_of_carry
#check FiniteMT.assertion16_of_carry
#print axioms FiniteMT.assertion16_of_carry
#check FiniteMT.depth_le_weight
#print axioms FiniteMT.depth_le_weight
#check FiniteMT.source_of_obligations
#print axioms FiniteMT.source_of_obligations

#print FiniteMT.SourceConjecture
#print FiniteMT.Conclusions
#print FiniteMT.CountDivisibility
#print FiniteMT.WeakCarryRecurrence
#print FiniteMT.Scaling12
#print FiniteMT.Scaling13
#print FiniteMT.Scaling14
#print FiniteMT.Divisibility15
#print FiniteMT.CountTheorem
#print FiniteMT.WeakLiftTheorem
```

### `DigitReindex.lean`

```lean
import Carry
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

open scoped BigOperators
noncomputable section
namespace FiniteMT

def joinDigits {d N p : ℕ} (x : Fin d → Fin N) (y : Fin d → Fin p) :
    Fin d → Fin (N*p) :=
  fun i => ⟨(x i).val + N*(y i).val, by
    have hx := (x i).isLt
    have hy := (y i).isLt
    nlinarith⟩

@[simp] theorem joinDigits_val {d N p : ℕ} (x : Fin d → Fin N)
    (y : Fin d → Fin p) (i : Fin d) :
    (joinDigits x y i).val = (x i).val + N*(y i).val := rfl

/-- Euclidean digits, without any sum or exponent restriction. -/
def digitTupleEquiv (d N p : ℕ) (hN : 0 < N) :
    ((Fin d → Fin N) × (Fin d → Fin p)) ≃ (Fin d → Fin (N*p)) where
  toFun z := joinDigits z.1 z.2
  invFun z := (fun i => ⟨(z i).val % N, Nat.mod_lt _ hN⟩,
    fun i => ⟨(z i).val / N, (Nat.div_lt_iff_lt_mul hN).mpr (by
      simpa only [Nat.mul_comm] using (z i).isLt)⟩)
  left_inv z := by
    apply Prod.ext
    · funext i
      apply Fin.ext
      exact (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt (z.1 i).isLt)
    · funext i
      apply Fin.ext
      change ((z.1 i).val + N*(z.2 i).val)/N = (z.2 i).val
      rw [Nat.add_mul_div_left _ _ hN, Nat.div_eq_of_lt (z.1 i).isLt, zero_add]
  right_inv z := by
    funext i
    apply Fin.ext
    exact Nat.mod_add_div _ _

theorem joinDigits_sum {d N p : ℕ} (x : Fin d → Fin N) (y : Fin d → Fin p) :
    (∑ i, (joinDigits x y i).val) = (∑ i, (x i).val)+N*∑ i, (y i).val := by
  simp only [joinDigits_val, Finset.sum_add_distrib, Finset.mul_sum]

theorem joinDigits_good {d N p : ℕ} (x : Fin d → Fin N) (y : Fin d → Fin p)
    (hpN : p ∣ N) :
    (∀ i, 0 < (joinDigits x y i).val ∧ ¬ p ∣ (joinDigits x y i).val) ↔
      (∀ i, 0 < (x i).val ∧ ¬ p ∣ (x i).val) := by
  have he (i : Fin d) : p ∣ (joinDigits x y i).val ↔ p ∣ (x i).val := by
    exact (Nat.dvd_add_iff_left (dvd_mul_of_dvd_left hpN _)).symm
  constructor
  · intro h i
    have hn := (he i).not.mp (h i).2
    refine ⟨?_, hn⟩
    by_contra hz
    have hx : (x i).val = 0 := by omega
    exact hn (hx ▸ dvd_zero p)
  · intro h i
    exact ⟨by have := (h i).1; simp only [joinDigits_val]; omega,
      (he i).not.mpr (h i).2⟩

/-- The low tuple's carry is in the full common range 1,...,d-1. -/
theorem low_carry_exists {d N p a : ℕ} (hN : 0 < N) (hd : 0 < d)
    (x : Fin d → Fin N) (y : Fin d → Fin p)
    (hx : ∀ i, 0 < (x i).val)
    (ht : (∑ i, (joinDigits x y i).val) = a*(N*p)) :
    ∃ b : Fin (d-1), (∑ i, (x i).val) = (b.val+1)*N ∧
      digitCondition p a (b.val+1) y := by
  let S := ∑ i, (x i).val
  let Y := ∑ i, (y i).val
  have hsum : S+N*Y = a*(N*p) := by simpa only [joinDigits_sum] using ht
  have hdiv : N ∣ S := by
    have : N ∣ S+N*Y := by rw [hsum]; exact ⟨a*p, by ring⟩
    exact (Nat.dvd_add_iff_left (dvd_mul_right N Y)).mpr this
  have hpos : 0 < S := by
    exact Finset.sum_pos (fun i _ => hx i) ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  have hlt : S < d*N := by
    calc
      S < ∑ _i : Fin d, N :=
        Finset.sum_lt_sum_of_nonempty (by exact ⟨⟨0, hd⟩, Finset.mem_univ _⟩)
          (fun i _ => (x i).isLt)
      _ = d*N := by simp
  obtain ⟨b, hb⟩ := hdiv
  have hbpos : 1 ≤ b := by nlinarith
  have hbd : b < d := by nlinarith
  refine ⟨⟨b-1, by omega⟩, ?_, ?_⟩
  · dsimp [S] at hb
    simpa only [Nat.sub_add_cancel hbpos, Nat.mul_comm] using hb
  · dsimp [digitCondition]
    have he : b+Y = a*p := by nlinarith
    simpa only [Nat.sub_add_cancel hbpos] using (by omega : Y+b = a*p)

/-- Filter identity used once by all precision versions of the lift. -/
theorem lift_filter {d N p a : ℕ} (hN : 0 < N) (hd : 0 < d) (hpN : p ∣ N)
    (x : Fin d → Fin N) (y : Fin d → Fin p) :
    ((∀ i, 0 < (joinDigits x y i).val ∧ ¬ p ∣ (joinDigits x y i).val) ∧
      (∑ i, (joinDigits x y i).val) = a*(N*p)) ↔
    ∃ b : Fin (d-1),
      ((∀ i, 0 < (x i).val ∧ ¬ p ∣ (x i).val) ∧
        (∑ i, (x i).val) = (b.val+1)*N) ∧ digitCondition p a (b.val+1) y := by
  rw [joinDigits_good x y hpN]
  constructor
  · rintro ⟨hx, ht⟩
    obtain ⟨b, hb, hy⟩ := low_carry_exists hN hd x y (fun i => (hx i).1) ht
    exact ⟨b, ⟨hx, hb⟩, hy⟩
  · rintro ⟨b, ⟨hx, ht⟩, hy⟩
    refine ⟨hx, ?_⟩
    rw [joinDigits_sum, ht]
    dsimp [digitCondition] at hy
    nlinarith

#print axioms digitTupleEquiv
#print axioms lift_filter
end FiniteMT
```

### `CountPolynomial.lean`

```lean
import Carry
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Linarith
open scoped BigOperators
open Polynomial
noncomputable section
namespace FiniteMT

def digitPoly (p : ℕ) : (ZMod p)[X] := ∑ y : Fin p, X ^ y.val

theorem digitPoly_eq (p : ℕ) (hp : p.Prime) :
    digitPoly p = (1-X)^(p-1) := by
  let : Fact p.Prime := ⟨hp⟩
  have hX : (1-X : (ZMod p)[X]) ≠ 0 := by
    intro h
    have := congrArg (fun f : (ZMod p)[X] => f.coeff 1) h
    norm_num [coeff_sub, coeff_one, coeff_X] at this
  apply mul_left_cancel₀ hX
  have hgeom : (1-X : (ZMod p)[X])*digitPoly p = 1-X^p := by
    unfold digitPoly
    rw [Fin.sum_univ_eq_sum_range]
    exact mul_neg_geom_sum (X : (ZMod p)[X]) p
  rw [hgeom, ← pow_succ', Nat.sub_add_cancel hp.one_le]
  rw [sub_pow_char, one_pow]

theorem digitPoly_power (p d : ℕ) :
    (digitPoly p)^d = ∑ y : Fin d → Fin p, X^(∑ i, (y i).val) := by
  classical
  calc
    _ = ∏ _i : Fin d, digitPoly p := by simp
    _ = ∑ y : Fin d → Fin p, ∏ i, (X : (ZMod p)[X])^(y i).val := by
      simp only [digitPoly]
      rw [Fintype.prod_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.prod_pow_eq_pow_sum]

theorem count_as_coeff (p d a b : ℕ) (hb : b ≤ a*p) :
    (carryCount p d a b : ZMod p) = ((digitPoly p)^d).coeff (a*p-b) := by
  classical
  rw [digitPoly_power, finsetSum_coeff]
  simp only [carryCount, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro y _
  have he : digitCondition p a b y ↔ a*p-b = ∑ i, (y i).val := by
    dsimp [digitCondition]; omega
  simp only [coeff_X_pow, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, he]

/-- A common coefficient gap: the high factor has only p-multiple degrees. -/
theorem expand_gap (p t k : ℕ) (hp : 0 < p) (ht : t < k % p)
    (f : (ZMod p)[X]) :
    ((expand (ZMod p) p f) * (1-X)^t).coeff k = 0 := by
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have he := Finset.mem_antidiagonal.mp hij
  by_cases hd : p ∣ ij.1
  · have hmod : k % p = ij.2 % p := by
      rw [← he, Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, zero_add, Nat.mod_mod]
    have hbound : t < ij.2 := by
      have := Nat.mod_le ij.2 p
      omega
    have hdeg : ((1-X : (ZMod p)[X])^t).natDegree ≤ t := by
      calc
        _ ≤ t*(1-X : (ZMod p)[X]).natDegree := natDegree_pow_le
        _ ≤ t*1 := Nat.mul_le_mul_left t (by
          exact (natDegree_sub_le_of_le (m:=1) (n:=1) (by norm_num) (natDegree_X_le)))
        _ = t := mul_one t
    rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hbound), mul_zero]
  · rw [coeff_expand hp, ite_eq_right hd, zero_mul]

theorem carryCount_dvd (p d a b : ℕ) (hp : p.Prime)
    (hd : d+1 < p) (ha : 1 ≤ a) (hb : 1 ≤ b) (hbd : b < d) :
    p ∣ carryCount p d a b := by
  let : Fact p.Prime := ⟨hp⟩
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  have hbp : b < p := by omega
  have hab : b ≤ a*p := by
    calc
      b ≤ p := by omega
      _ ≤ a*p := by simpa using Nat.mul_le_mul_right p ha
  rw [count_as_coeff p d a b hab, digitPoly_eq p hp, ← pow_mul]
  have hexp : (p-1)*d = p*(d-1)+(p-d) := by
    have : 1 ≤ d := by omega
    have hp1 : p-1+1 = p := Nat.sub_add_cancel hp.one_le
    have hd1 : d-1+1 = d := Nat.sub_add_cancel (by omega)
    have hpd : p-d+d = p := Nat.sub_add_cancel (by omega)
    nlinarith
  rw [hexp, pow_add, pow_mul]
  have hfrob : (1-X : (ZMod p)[X])^p = 1-X^p := by rw [sub_pow_char, one_pow]
  rw [hfrob]
  have he : (1-X^p : (ZMod p)[X])^(d-1) =
      expand (ZMod p) p ((1-X)^(d-1)) := by simp
  rw [he]
  apply expand_gap p (p-d) (a*p-b) hp.pos
  have hrem : (a*p-b)%p = p-b := by
    have he : a*p-b = (a-1)*p+(p-b) := by
      have ha1 := Nat.sub_add_cancel ha
      have hpb := Nat.sub_add_cancel (Nat.le_of_lt hbp)
      have hab1 := Nat.sub_add_cancel hab
      nlinarith
    rw [he, Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_eq_of_lt (by omega : p-b < p), Nat.mod_eq_of_lt (by omega : p-b < p)]
  rw [hrem]
  omega

#print axioms carryCount_dvd
end FiniteMT
```

### `InverseCongruence.lean`

```lean
import ModularTaylor
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Ring.Finset
open scoped BigOperators
noncomputable section
namespace FiniteMT

theorem unit_inverse_sub {R : Type*} [CommRing R] (h : R) (u v : Rˣ)
    (hv : h ∣ (u:R)-(v:R)) : h ∣ (↑u⁻¹:R)-(↑v⁻¹:R) := by
  have he : (↑u⁻¹:R)-(↑v⁻¹:R) =
      (-((↑u⁻¹:R)*(↑v⁻¹:R)))*((u:R)-(v:R)) := by
    calc
      _ = (↑u⁻¹:R)*((v:R)*(↑v⁻¹:R))-
          ((u:R)*(↑u⁻¹:R))*(↑v⁻¹:R) := by simp
      _ = _ := by ring
  rw [he]
  exact dvd_mul_of_dvd_right hv _

theorem product_sub_dvd {R I : Type*} [CommRing R] (t : Finset I)
    (f g : I → R) (h : R) (he : ∀ i ∈ t, h ∣ f i-g i) :
    h ∣ (∏ i ∈ t, f i)-(∏ i ∈ t, g i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    have he1 := he i (Finset.mem_insert_self i t)
    have he2 := ih (fun j hj => he j (Finset.mem_insert_of_mem hj))
    have hex : f i*(∏ j ∈ t, f j)-g i*(∏ j ∈ t, g j) =
        (f i-g i)*(∏ j ∈ t, f j)+g i*((∏ j ∈ t, f j)-(∏ j ∈ t, g j)) := by ring
    rw [hex]
    exact dvd_add (dvd_mul_of_dvd_left he1 _) (dvd_mul_of_dvd_right he2 _)

/-- Only unit inversion is used, so the result is valid at every precision k. -/
theorem inverse_product_lift_dvd (p r k d : ℕ) (hp : p.Prime) (hk : 0 < k)
    (s x y : Fin d → ℕ)
    (hx : ∀ i, ¬ p ∣ x i) :
    (p : ZMod (p^k))^r ∣
      (∏ i, (((x i+p^r*y i : ℕ) : ZMod (p^k))⁻¹)^s i) -
        (∏ i, (((x i : ℕ) : ZMod (p^k))⁻¹)^s i) := by
  by_cases hr : r=0
  · simp [hr]
  apply product_sub_dvd
  intro i _
  apply dvd_trans _ (sub_dvd_pow_sub_pow _ _ _)
  have hplus : ¬ p ∣ x i+p^r*y i := by
    have hpr : p ∣ p^r := dvd_pow_self p hr
    exact fun h => hx i ((Nat.dvd_add_iff_left (dvd_mul_of_dvd_left hpr _)).mpr h)
  obtain ⟨u, hu⟩ := Taylor.coordinate_isUnit p k (x i+p^r*y i) hp hk hplus
  obtain ⟨v, hv⟩ := Taylor.coordinate_isUnit p k (x i) hp hk (hx i)
  rw [← hu, ← hv, ZMod.inv_coe_unit, ZMod.inv_coe_unit]
  apply unit_inverse_sub
  rw [hu, hv, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, add_sub_cancel_left]
  exact dvd_mul_right _ _

end FiniteMT
```

### `CarryReindex.lean`

```lean
import DigitReindex
open scoped BigOperators
noncomputable section
namespace FiniteMT

def lowCondition {d : ℕ} (p N b : ℕ) (x : Fin d → Fin N) : Prop :=
  (∀ i, 0 < (x i).val ∧ ¬ p ∣ (x i).val) ∧ (∑ i, (x i).val) = b*N

instance {d : ℕ} (p N b : ℕ) (x : Fin d → Fin N) :
    Decidable (lowCondition p N b x) := by unfold lowCondition; infer_instance

/-- All carry and digit reindexing is independent of the summand and its precision. -/
theorem sum_lift_reindex {R : Type*} [AddCommMonoid R] (p N d a : ℕ)
    (hN : 0 < N) (hd : 0 < d) (hpN : p ∣ N)
    (W : (Fin d → Fin (N*p)) → R) :
    (∑ z : Fin d → Fin (N*p),
      if (∀ i, 0 < (z i).val ∧ ¬ p ∣ (z i).val) ∧
        (∑ i, (z i).val) = a*(N*p) then W z else 0) =
    ∑ b : Fin (d-1), ∑ x : Fin d → Fin N, ∑ y : Fin d → Fin p,
      if lowCondition p N (b.val+1) x ∧ digitCondition p a (b.val+1) y
      then W (joinDigits x y) else 0 := by
  classical
  rw [← Equiv.sum_comp (digitTupleEquiv d N p hN)]
  simp only [Fintype.sum_prod_type, digitTupleEquiv, Equiv.coe_fn_mk]
  have hi (x : Fin d → Fin N) (y : Fin d → Fin p) :
      (if (∀ i, 0 < (joinDigits x y i).val ∧ ¬ p ∣ (joinDigits x y i).val) ∧
        (∑ i, (joinDigits x y i).val) = a*(N*p) then W (joinDigits x y) else 0) =
      ∑ b : Fin (d-1),
        if lowCondition p N (b.val+1) x ∧ digitCondition p a (b.val+1) y
        then W (joinDigits x y) else 0 := by
    simp only [lift_filter hN hd hpN x y]
    change (if ∃ b : Fin (d-1),
      lowCondition p N (b.val+1) x ∧ digitCondition p a (b.val+1) y
      then _ else _) = _
    split_ifs with hex
    · obtain ⟨b, hb⟩ := hex
      rw [Finset.sum_eq_single b]
      · simp [hb]
      · intro c _ hcb
        apply ite_eq_right
        rintro ⟨hc, _⟩
        apply hcb
        apply Fin.ext
        have hb' := hb.1.2
        have hc' := hc.2
        nlinarith
      · simp
    · symm
      apply Finset.sum_eq_zero
      intro b _
      exact ite_eq_right (fun hb => hex ⟨b, hb⟩)
  simp_rw [hi]
  calc
    _ = ∑ x, ∑ b : Fin (d-1), ∑ y,
        if lowCondition p N (b.val+1) x ∧ digitCondition p a (b.val+1) y
        then W (joinDigits x y) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

/-- The source sum rewritten into the same fibers used by both Taylor orders. -/
theorem carrySum_reindex (p r k d a : ℕ) (s : Fin d → ℕ)
    (hp : 0 < p) (hr : 1 ≤ r) (hd : 0 < d) :
    carrySum p (r+1) k s a =
    ∑ b : Fin (d-1), ∑ x : Fin d → Fin (p^r), ∑ y : Fin d → Fin p,
      if lowCondition p (p^r) (b.val+1) x ∧ digitCondition p a (b.val+1) y
      then ∏ i, (((joinDigits x y i).val : ZMod (p^k))⁻¹)^s i else 0 := by
  unfold carrySum
  simp only [pow_succ p r]
  exact sum_lift_reindex p (p^r) d a (pow_pos hp _) hd
    (dvd_pow_self p (by omega)) _

#print axioms sum_lift_reindex
#print axioms carrySum_reindex
end FiniteMT
```

### `WeakLift.lean`

```lean
import CarryReindex
import InverseCongruence
import WeakInduction
open scoped BigOperators
noncomputable section
namespace FiniteMT

theorem digit_constant_sum {R : Type*} [CommSemiring R] (p d a b : ℕ) (v : R) :
    (∑ y : Fin d → Fin p, if digitCondition p a b y then v else 0) =
      (carryCount p d a b : R)*v := by
  classical
  simp only [carryCount, Nat.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> simp

theorem base_lift_sum (p r k d a : ℕ) (s : Fin d → ℕ) :
    (∑ b : Fin (d-1), ∑ x : Fin d → Fin (p^r), ∑ y : Fin d → Fin p,
      if lowCondition p (p^r) (b.val+1) x ∧ digitCondition p a (b.val+1) y
      then ∏ i, (((x i).val : ZMod (p^k))⁻¹)^s i else 0) =
    ∑ b : Fin (d-1), (carryCount p d a (b.val+1) : ZMod (p^k)) *
      carrySum p r k s (b.val+1) := by
  classical
  apply Finset.sum_congr rfl
  intro b _
  simp only [carrySum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  change (∑ y, if lowCondition p (p^r) (b.val+1) x ∧
      digitCondition p a (b.val+1) y then _ else _) =
    _ * (if lowCondition p (p^r) (b.val+1) x then _ else _)
  by_cases hx : lowCondition p (p^r) (b.val+1) x
  · simp only [hx, true_and, ite_true]
    exact digit_constant_sum _ _ _ _ _
  · simp only [hx, false_and, ite_false, Finset.sum_const_zero, mul_zero]

/-- The actual carry recurrence at first precision, with no weight restriction. -/
theorem weakCarryRecurrence (p d k : ℕ) (hp : p.Prime) :
    WeakCarryRecurrence p d k := by
  classical
  intro r hr s a _ had
  by_cases hk : k=0
  · subst k
    have he : carrySum p (r+1) 0 s a -
        ∑ b : Fin (d-1), (carryCount p d a (b.val+1) : ZMod (p^0)) *
          carrySum p r 0 s (b.val+1) = 0 := by
      let : Subsingleton (ZMod (p^0)) := ZMod.subsingleton_iff.mpr (pow_zero p)
      exact Subsingleton.elim _ _
    rw [he]
    exact dvd_zero _
  have hd : 0 < d := by omega
  rw [carrySum_reindex p r k d a s hp.pos hr hd, ← base_lift_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro b _
  rw [← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro x _
  rw [← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro y _
  by_cases hf : lowCondition p (p^r) (b.val+1) x ∧ digitCondition p a (b.val+1) y
  · simp only [hf, true_and, ite_true, joinDigits_val]
    exact inverse_product_lift_dvd p r k d hp (by omega) s
      (fun i => (x i).val) (fun i => (y i).val) (fun i => (hf.1.1 i).2)
  · simp only [hf, ite_false, sub_self, dvd_zero]

#print axioms weakCarryRecurrence
end FiniteMT
```

### `Assertion16.lean`

```lean
import CountPolynomial
import WeakLift
import Obligations
namespace FiniteMT

theorem countTheorem : CountTheorem := by
  intro p d hp hd a b ha _ hb hbd
  exact carryCount_dvd p d a b hp hd ha hb hbd

theorem weakLiftTheorem : WeakLiftTheorem := by
  intro p d k hp _
  exact weakCarryRecurrence p d k hp

/-- Unconditional source (16), with its exact source hypotheses.
In fact neither the exponent positivity nor the parity is needed once p>d+1. -/
theorem assertion16 (p r d : ℕ) (s : Fin d → ℕ)
    (hp : p.Prime) (hr : 2 ≤ r) (hd : 0 < d)
    (hs : ∀ i, 0 < s i) (hw : weight s+1 < p) :
    sumMod p r (r-1) s = 0 := by
  have hdp : d+1 < p :=
    lt_of_le_of_lt (Nat.add_le_add_right (depth_le_weight s hs) 1) hw
  exact assertion16_of_carry p r d s hr hd
    (countTheorem p d hp hdp) (weakCarryRecurrence p d (r-1) hp)

/-- The former six inputs have been reduced to the four non-routine clauses. -/
theorem source_of_four (h12 : Scaling12) (h13 : Scaling13) (h14 : Scaling14)
    (h15 : Divisibility15) : SourceConjecture :=
  source_of_obligations h12 h13 h14 h15 countTheorem weakLiftTheorem

theorem firstMoment_dvd (p d a b : ℕ) (i : Fin d) (hp : p.Prime)
    (hd : d+1 < p) (ha : 1 ≤ a) (hb : 1 ≤ b) (hbd : b < d) :
    p ∣ firstMoment p d a b i := by
  have hdp : ¬ p ∣ d := Nat.not_dvd_of_pos_of_lt (by have := i.isLt; omega) (by omega)
  exact firstMoment_dvd_of_count p d a b i hp hdp (carryCount_dvd p d a b hp hd ha hb hbd)

#print axioms countTheorem
#print axioms weakLiftTheorem
#print axioms assertion16
#print axioms source_of_four
#print axioms firstMoment_dvd
end FiniteMT
```

### `MomentPolynomial.lean`

```lean
import CountPolynomial
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
open scoped BigOperators
open Polynomial
noncomputable section
namespace FiniteMT

def weightedDigitPoly (p e : ℕ) : (ZMod p)[X] :=
  ∑ t : Fin p, C ((t.val : ZMod p)^e)*X^t.val

theorem weighted_product (p d : ℕ) (w : Fin d → Fin p → ZMod p) :
    (∏ i, ∑ t : Fin p, C (w i t)*X^t.val) =
      ∑ y : Fin d → Fin p, C (∏ i, w i (y i))*X^(∑ i, (y i).val) := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]

theorem prod_one_factor {R : Type*} [CommMonoid R] (d : ℕ) (i : Fin d)
    (A F : R) :
    (∏ j : Fin d, if j=i then A else F) = A*F^(d-1) := by
  classical
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [ite_true]
  congr 1
  calc
    _ = ∏ _j ∈ Finset.univ.erase i, F := by
      apply Finset.prod_congr rfl
      intro j hj
      exact ite_eq_right (Finset.ne_of_mem_erase hj)
    _ = _ := by simp

theorem prod_two_factor {R : Type*} [CommMonoid R] (d : ℕ) (i j : Fin d)
    (hij : i ≠ j) (A B F : R) :
    (∏ l : Fin d, if l=i then A else if l=j then B else F) =
      A*B*F^(d-2) := by
  classical
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [ite_true]
  have hj : j ∈ Finset.univ.erase i := by simp [hij.symm]
  rw [← Finset.mul_prod_erase _ _ hj]
  simp only [hij.symm, ite_false, ite_true]
  rw [mul_assoc]
  congr 1
  congr 1
  calc
    _ = ∏ _l ∈ (Finset.univ.erase i).erase j, F := by
      apply Finset.prod_congr rfl
      intro l hl
      have hli := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hl)
      have hlj := Finset.ne_of_mem_erase hl
      simp only [hli, hlj, ite_false]
    _ = _ := by simp [Finset.card_erase_of_mem hj, Nat.sub_sub]

theorem one_moment_poly (p d e : ℕ) (i : Fin d) :
    (∑ y : Fin d → Fin p, C (((y i).val : ZMod p)^e)*X^(∑ l, (y l).val)) =
      weightedDigitPoly p e * (digitPoly p)^(d-1) := by
  classical
  have h := weighted_product p d (fun l t => if l=i then (t.val:ZMod p)^e else 1)
  have hs : (∑ y : Fin d → Fin p,
      C (∏ l, if l=i then ((y l).val:ZMod p)^e else 1)*X^(∑ l, (y l).val)) =
      ∑ y : Fin d → Fin p, C (((y i).val:ZMod p)^e)*X^(∑ l, (y l).val) := by
    simp only [Fintype.prod_ite_eq']
  rw [hs] at h
  rw [← h]
  calc
    _ = ∏ l : Fin d, if l=i then weightedDigitPoly p e else digitPoly p := by
      apply Finset.prod_congr rfl
      intro l _
      by_cases hl : l=i
      · simp only [hl, ite_true, weightedDigitPoly]
      · simp only [hl, ite_false, C_1, one_mul, digitPoly]
    _ = _ := prod_one_factor _ _ _ _

theorem mixed_moment_poly (p d : ℕ) (i j : Fin d) (hij : i ≠ j) :
    (∑ y : Fin d → Fin p,
      C (((y i).val:ZMod p)*((y j).val:ZMod p))*X^(∑ l, (y l).val)) =
      weightedDigitPoly p 1 * weightedDigitPoly p 1 * (digitPoly p)^(d-2) := by
  classical
  let w : Fin d → Fin p → ZMod p :=
    fun l t => (if l=i then (t.val:ZMod p) else 1)*(if l=j then (t.val:ZMod p) else 1)
  have hw (y : Fin d → Fin p) :
      (∏ l, w l (y l)) = ((y i).val:ZMod p)*((y j).val:ZMod p) := by
    dsimp [w]
    rw [Finset.prod_mul_distrib]
    simp only [Fintype.prod_ite_eq']
  have h := weighted_product p d w
  simp only [hw] at h
  rw [← h]
  calc
    _ = ∏ l : Fin d, if l=i then weightedDigitPoly p 1 else
        if l=j then weightedDigitPoly p 1 else digitPoly p := by
      apply Finset.prod_congr rfl
      intro l _
      by_cases hli : l=i
      · subst l
        simp only [w, hij, ite_true, ite_false, mul_one, weightedDigitPoly, pow_one]
      · by_cases hlj : l=j
        · subst l
          simp only [w, hij.symm, ite_false, ite_true, one_mul, weightedDigitPoly, pow_one]
        · simp only [w, hli, hlj, ite_false, mul_one, C_1, one_mul, digitPoly]
    _ = _ := prod_two_factor _ _ _ hij _ _ _

theorem weightedDigitPoly_one (p : ℕ) :
    weightedDigitPoly p 1 = X*derivative (digitPoly p) := by
  simp only [weightedDigitPoly, digitPoly, map_sum, derivative_X_pow, pow_one,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : t.val=0
  · simp [ht]
  · have he : t.val-1+1=t.val := Nat.sub_add_cancel (by omega)
    rw [← mul_assoc, mul_comm X (C _), mul_assoc, ← pow_succ', he]

theorem weightedDigitPoly_two (p : ℕ) :
    weightedDigitPoly p 2 = X^2*derivative (derivative (digitPoly p)) +
      X*derivative (digitPoly p) := by
  simp only [weightedDigitPoly, digitPoly, map_sum, derivative_X_pow,
    derivative_mul, derivative_C, zero_mul, zero_add, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  rcases t with ⟨t, ht⟩
  rcases t with _ | t
  · simp
  rcases t with _ | t
  · norm_num
  · simp only [Nat.cast_add, Nat.cast_one]
    have h1 : t+1+1-1 = t+1 := by omega
    have h2 : t+1-1 = t := by omega
    simp only [h1, h2, Nat.cast_add, Nat.cast_one]
    simp only [← mul_assoc, ← C_mul]
    simp only [map_add, map_mul, map_pow, C_1]
    ring

#print axioms one_moment_poly
#print axioms mixed_moment_poly
end FiniteMT
```

### `MomentGap.lean`

```lean
import CountPolynomial
open Polynomial
noncomputable section
namespace FiniteMT

/-- One coefficient-gap lemma for all zeroth, first and second moments. -/
theorem moment_gap (p d a b q : ℕ) (hp : p.Prime) (hd : d+1 < p)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hbd : b < d) (hq : q ≤ 2) :
    ((X^q : (ZMod p)[X])*(1-X)^((p-1)*d-q)).coeff (a*p-b) = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  have hbp : b < p := by omega
  have hqp : q < p-b := by omega
  have hap : p ≤ a*p := by simpa using Nat.mul_le_mul_right p ha
  have hab : b ≤ a*p := by omega
  have hqn : q ≤ a*p-b := by omega
  rw [coeff_X_pow_mul', ite_eq_left hqn]
  have hp1 := Nat.sub_add_cancel hp.one_le
  have hd1 : d-1+1=d := Nat.sub_add_cancel (by omega)
  have hpd : p-d-q+(d+q)=p := by omega
  have hmul : q ≤ (p-1)*d := by nlinarith
  have hmq := Nat.sub_add_cancel hmul
  have hexp : (p-1)*d-q = p*(d-1)+(p-d-q) := by nlinarith
  rw [hexp, pow_add, pow_mul]
  have hfrob : (1-X : (ZMod p)[X])^p = 1-X^p := by rw [sub_pow_char, one_pow]
  rw [hfrob]
  have he : (1-X^p : (ZMod p)[X])^(d-1) =
      expand (ZMod p) p ((1-X)^(d-1)) := by simp
  rw [he]
  apply expand_gap p (p-d-q) (a*p-b-q) hp.pos
  have hrem : (a*p-b-q)%p = p-b-q := by
    have ha1 := Nat.sub_add_cancel ha
    have hpb := Nat.sub_add_cancel (Nat.le_of_lt hbp)
    have hab1 := Nat.sub_add_cancel hab
    have hqn1 := Nat.sub_add_cancel hqn
    have hpq : p-b-q+(b+q)=p := by omega
    have he : a*p-b-q = (a-1)*p+(p-b-q) := by nlinarith
    rw [he, Nat.add_mod, Nat.mul_mod_left, zero_add,
      Nat.mod_eq_of_lt (by omega : p-b-q < p),
      Nat.mod_eq_of_lt (by omega : p-b-q < p)]
  rw [hrem]
  omega

#print axioms moment_gap
end FiniteMT
```

### `ConcreteMoments.lean`

```lean
import MomentPolynomial
import MomentGap
open scoped BigOperators
open Polynomial
noncomputable section
namespace FiniteMT

theorem digitPoly_derivative (p : ℕ) (hp : p.Prime) :
    derivative (digitPoly p) = (1-X)^(p-2) := by
  let : Fact p.Prime := ⟨hp⟩
  rw [digitPoly_eq p hp, derivative_pow]
  simp [derivative_sub, Nat.cast_sub hp.one_le, Nat.sub_sub]

theorem digitPoly_derivative_two (p : ℕ) (hp : p.Prime) :
    derivative (derivative (digitPoly p)) = C (2 : ZMod p)*(1-X)^(p-3) := by
  let : Fact p.Prime := ⟨hp⟩
  rw [digitPoly_derivative p hp, derivative_pow]
  simp [derivative_sub, Nat.cast_sub hp.two_le, Nat.sub_sub]

/-- Coefficient bridge for arbitrary natural weights, including all moments. -/
theorem fiber_weight_coeff (p d a b : ℕ) (hb : b ≤ a*p)
    (w : (Fin d → Fin p) → ℕ) :
    (∑ y : Fin d → Fin p, if digitCondition p a b y then (w y : ZMod p) else 0) =
      (∑ y : Fin d → Fin p, C (w y : ZMod p)*X^(∑ l, (y l).val)).coeff (a*p-b) := by
  classical
  rw [finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro y _
  have he : digitCondition p a b y ↔ a*p-b = ∑ l, (y l).val := by
    dsimp [digitCondition]; omega
  simp only [coeff_C_mul, coeff_X_pow, he]
  split_ifs <;> simp

theorem mixed_secondMoment_dvd (p d a b : ℕ) (i j : Fin d) (hij : i ≠ j)
    (hp : p.Prime) (hd : d+1 < p) (ha : 1 ≤ a) (hb : 1 ≤ b) (hbd : b < d) :
    p ∣ secondMoment p d a b i j := by
  let : Fact p.Prime := ⟨hp⟩
  have hd2 : 2 ≤ d := by
    by_contra h
    have hi := i.isLt
    have hj := j.isLt
    have : i=j := Fin.ext (by omega)
    exact hij this
  have hab : b ≤ a*p := by
    have : p ≤ a*p := by simpa using Nat.mul_le_mul_right p ha
    omega
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  simp only [secondMoment, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
  rw [fiber_weight_coeff p d a b hab, show
    (∑ y : Fin d → Fin p, C (((y i).val*(y j).val : ℕ):ZMod p)*X^(∑ l, (y l).val)) =
      weightedDigitPoly p 1 * weightedDigitPoly p 1 * (digitPoly p)^(d-2) by
        simp only [Nat.cast_mul]; exact mixed_moment_poly p d i j hij]
  rw [weightedDigitPoly_one, digitPoly_derivative p hp, digitPoly_eq p hp]
  have he : p-2+(p-2)+(p-1)*(d-2) = (p-1)*d-2 := by
    have hp2 := Nat.sub_add_cancel hp.two_le
    have hd2' := Nat.sub_add_cancel hd2
    have hp1 := Nat.sub_add_cancel hp.one_le
    have hm : 2 ≤ (p-1)*d := by nlinarith
    have hm' := Nat.sub_add_cancel hm
    nlinarith
  have halg : (X*(1-X)^(p-2))*(X*(1-X)^(p-2))*
      ((1-X)^(p-1))^(d-2) =
      (X^2 : (ZMod p)[X])*(1-X)^((p-1)*d-2) := by
    rw [← pow_mul, ← he]
    simp only [pow_add]
    ring
  rw [halg]
  exact moment_gap p d a b 2 hp hd ha hb hbd (by omega)

theorem square_secondMoment_dvd (p d a b : ℕ) (i : Fin d)
    (hp : p.Prime) (hd : d+1 < p) (ha : 1 ≤ a) (hb : 1 ≤ b) (hbd : b < d) :
    p ∣ secondMoment p d a b i i := by
  let : Fact p.Prime := ⟨hp⟩
  have hab : b ≤ a*p := by
    have : p ≤ a*p := by simpa using Nat.mul_le_mul_right p ha
    omega
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  simp only [secondMoment, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
  rw [fiber_weight_coeff p d a b hab]
  simp only [← pow_two, Nat.cast_pow]
  rw [one_moment_poly, weightedDigitPoly_two, digitPoly_derivative_two p hp,
    digitPoly_derivative p hp, digitPoly_eq p hp]
  have he1 : p-2+(p-1)*(d-1) = (p-1)*d-1 := by
    have hp2 := Nat.sub_add_cancel hp.two_le
    have hd1 : d-1+1=d := Nat.sub_add_cancel (by omega)
    have hp1 := Nat.sub_add_cancel hp.one_le
    have hm : 1 ≤ (p-1)*d := by nlinarith
    have hm' := Nat.sub_add_cancel hm
    nlinarith
  have hp3 : 3 ≤ p := by omega
  have he2 : p-3+(p-1)*(d-1) = (p-1)*d-2 := by
    have hp3' := Nat.sub_add_cancel hp3
    have hd1 : d-1+1=d := Nat.sub_add_cancel (by omega)
    have hp1 := Nat.sub_add_cancel hp.one_le
    have hm : 2 ≤ (p-1)*d := by nlinarith
    have hm' := Nat.sub_add_cancel hm
    nlinarith
  have halg : (X^2*(C (2:ZMod p)*(1-X)^(p-3))+X*(1-X)^(p-2))*
      ((1-X)^(p-1))^(d-1) =
      C (2:ZMod p)*(X^2*(1-X)^((p-1)*d-2))+
        X^1*(1-X)^((p-1)*d-1) := by
    rw [← pow_mul, ← he1, ← he2]
    simp only [pow_add, pow_one]
    ring
  rw [halg, coeff_add, coeff_C_mul,
    moment_gap p d a b 2 hp hd ha hb hbd (by omega),
    moment_gap p d a b 1 hp hd ha hb hbd (by omega), mul_zero, add_zero]

theorem secondMoment_dvd (p d a b : ℕ) (i j : Fin d)
    (hp : p.Prime) (hd : d+1 < p) (ha : 1 ≤ a) (hb : 1 ≤ b) (hbd : b < d) :
    p ∣ secondMoment p d a b i j := by
  by_cases hij : i=j
  · subst j
    exact square_secondMoment_dvd p d a b i hp hd ha hb hbd
  · exact mixed_secondMoment_dvd p d a b i j hij hp hd ha hb hbd

#print axioms secondMoment_dvd
end FiniteMT
```

### `CarryReflection.lean`

```lean
import Carry
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic.Linarith
open scoped BigOperators
noncomputable section
namespace FiniteMT

def reflectDigits (p d : ℕ) : (Fin d → Fin p) ≃ (Fin d → Fin p) where
  toFun y i := (y i).rev
  invFun y i := (y i).rev
  left_inv y := by funext i; simp
  right_inv y := by funext i; simp

theorem reflectDigits_total (p d : ℕ) (y : Fin d → Fin p) :
    (∑ i, ((reflectDigits p d y) i).val) + (∑ i, (y i).val) = d*(p-1) := by
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ _i : Fin d, (p-1) := by
      apply Finset.sum_congr rfl
      intro i _
      change (y i).rev.val+(y i).val = p-1
      rw [Fin.val_rev]
      have := (y i).isLt
      omega
    _ = _ := by simp

theorem digitCondition_reflect (p d a b : ℕ) (hp : 0 < p)
    (ha : a ≤ d) (hb : b ≤ d) (y : Fin d → Fin p) :
    digitCondition p (d-a) (d-b) (reflectDigits p d y) ↔ digitCondition p a b y := by
  dsimp [digitCondition]
  have hsum := reflectDigits_total p d y
  have hp1 := Nat.sub_add_cancel hp
  have ha1 := Nat.sub_add_cancel ha
  have hb1 := Nat.sub_add_cancel hb
  constructor <;> intro h <;> nlinarith

theorem carryCount_reflection (p d a b : ℕ) (hp : 0 < p) (ha : a ≤ d) (hb : b ≤ d) :
    carryCount p d (d-a) (d-b) = carryCount p d a b := by
  unfold carryCount
  rw [← Equiv.sum_comp (reflectDigits p d)]
  simp only [digitCondition_reflect p d a b hp ha hb]

#print axioms carryCount_reflection
end FiniteMT
```

### `CarryFiber.lean`

```lean
import ConcreteMoments
import UniformLift
import Assertion16
open scoped BigOperators
noncomputable section
namespace FiniteMT

abbrev DigitFiber (p d a b : ℕ) :=
  {y : Fin d → Fin p // digitCondition p a b y}

theorem digitFiber_sum {R : Type*} [AddCommMonoid R] (p d a b : ℕ)
    (f : (Fin d → Fin p) → R) :
    (∑ y : DigitFiber p d a b, f y.val) =
      ∑ y : Fin d → Fin p, if digitCondition p a b y then f y else 0 := by
  classical
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) f).symm

theorem digitFiber_card (p d a b : ℕ) :
    Fintype.card (DigitFiber p d a b) = carryCount p d a b := by
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, carryCount]
    using digitFiber_sum p d a b (fun _ => (1:ℕ))

theorem digitFiber_first (p d a b k : ℕ) (i : Fin d) :
    (∑ y : DigitFiber p d a b, ((y.val i).val : ZMod (p^k))) =
      (firstMoment p d a b i : ZMod (p^k)) := by
  rw [digitFiber_sum p d a b (fun y => ((y i).val : ZMod (p^k)))]
  simp only [firstMoment, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]

theorem digitFiber_second (p d a b k : ℕ) (i j : Fin d) :
    (∑ y : DigitFiber p d a b,
      ((y.val i).val : ZMod (p^k))*((y.val j).val : ZMod (p^k))) =
      (secondMoment p d a b i j : ZMod (p^k)) := by
  rw [digitFiber_sum p d a b (fun y => ((y i).val : ZMod (p^k))*((y j).val : ZMod (p^k)))]
  simp only [secondMoment, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_mul]

theorem linear_eq_sum {R : Type*} [CommRing R] (cs : List (R × R)) :
    Taylor.linear cs = (cs.map Prod.fst).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [Taylor.linear, ih]

/-- Uniform concrete Taylor fiber; no moment hypotheses remain. -/
theorem concrete_lifted_fiber (p r d a b : ℕ) (s x : Fin d → ℕ) (i0 : Fin d)
    (hp : p.Prime) (hr : 1 ≤ r) (hd : d+1 < p)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hbd : b < d) (hx : ∀ i, ¬ p ∣ x i) :
    (∑ y : DigitFiber p d a b,
      ∏ i, (((x i+p^r*(y.val i).val : ℕ) : ZMod (p^(2*r+1)))⁻¹)^s i) =
      (∏ i, ((x i : ZMod (p^(2*r+1)))⁻¹)^s i) *
        ((carryCount p d a b : ZMod (p^(2*r+1))) -
          (p : ZMod (p^(2*r+1)))^r*(firstMoment p d a b i0 : ZMod (p^(2*r+1)))*
            ∑ i, (s i : ZMod (p^(2*r+1)))*(x i : ZMod (p^(2*r+1)))⁻¹) := by
  classical
  let A := ZMod (p^(2*r+1))
  obtain ⟨u, hu⟩ : ∃ u : Fin d → Aˣ, ∀ i, (u i : A) = (x i : A) := by
    choose u hu using fun i => Taylor.coordinate_isUnit p (2*r+1) (x i) hp (by omega) (hx i)
    exact ⟨u, hu⟩
  let digits : Fin d → DigitFiber p d a b → A := fun i y => ((y.val i).val : A)
  have hm (i j : Fin d) : (p:A) ∣ ∑ y, digits i y*digits j y := by
    change (p:A) ∣ ∑ y : DigitFiber p d a b,
      ((y.val i).val : A)*((y.val j).val : A)
    rw [digitFiber_second]
    obtain ⟨c, hc⟩ := secondMoment_dvd p d a b i j hp hd ha hb hbd
    exact ⟨(c:A), by rw [hc, Nat.cast_mul]⟩
  have ht := Taylor.modular_lifted_sum p r d hr u s digits hm
  dsimp only at ht
  have huinv (i : Fin d) : (↑(u i)⁻¹ : A) = (x i : A)⁻¹ := by
    rw [← ZMod.inv_coe_unit, hu]
  have hlin : (∑ y : DigitFiber p d a b,
      Taylor.linear (Taylor.evaluate
        ((List.ofFn fun i => (u i, digits i, s i)).map Taylor.familyCoeff) y)) =
      -(firstMoment p d a b i0 : A)*∑ i, (s i:A)*(x i:A)⁻¹ := by
    simp only [linear_eq_sum, Taylor.evaluate, List.map_ofFn,
      Function.comp_def, List.sum_ofFn]
    simp only [Taylor.familyCoeff_first, Taylor.firstConstant]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hdigit (i : Fin d) : (∑ y : DigitFiber p d a b, digits i y) =
        (firstMoment p d a b i0 : A) := by
      change (∑ y : DigitFiber p d a b, ((y.val i).val:A)) = _
      rw [digitFiber_first, firstMoment_symm p d a b i i0]
    simp_rw [hdigit, huinv]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hlin, digitFiber_card] at ht
  simp only [hu, huinv] at ht
  have hcast (y : DigitFiber p d a b) (i : Fin d) :
      ((x i+p^r*(y.val i).val : ℕ):A) = (x i:A)+(p:A)^r*digits i y := by
    dsimp [A, digits]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  simp_rw [hcast]
  convert ht using 1; ring

#print axioms concrete_lifted_fiber
end FiniteMT
```

### `DoubleLift.lean`

```lean
import CarryFiber
import CarryReindex
open scoped BigOperators
noncomputable section
namespace FiniteMT

def shiftExponent {d : ℕ} (s : Fin d → ℕ) (i : Fin d) : Fin d → ℕ :=
  Function.update s i (s i+1)

def derivativeCarrySum (p r k : ℕ) {d : ℕ} (s : Fin d → ℕ) (b : ℕ) :
    ZMod (p^k) := ∑ i, (s i : ZMod (p^k))*carrySum p r k (shiftExponent s i) b

theorem shifted_product {R : Type*} [CommMonoid R] (d : ℕ)
    (f : Fin d → R) (s : Fin d → ℕ) (i : Fin d) :
    (∏ j, f j ^ shiftExponent s i j) = (∏ j, f j ^ s j)*f i := by
  classical
  have he : (fun j => f j ^ shiftExponent s i j) =
      Function.update (fun j => f j ^ s j) i (f i ^ (s i+1)) := by
    funext j
    by_cases hj : j=i <;> simp [shiftExponent, hj]
  rw [he, Finset.prod_update_of_mem (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase _ (fun j => f j ^ s j) (Finset.mem_univ i), pow_succ]
  simp only [Finset.sdiff_singleton_eq_erase]
  ac_rfl

theorem product_derivative_sum (p r k d b : ℕ) (s : Fin d → ℕ) :
    (∑ x : Fin d → Fin (p^r), if lowCondition p (p^r) b x then
      (∏ i, ((x i).val : ZMod (p^k))⁻¹ ^ s i) *
        (∑ i, (s i : ZMod (p^k))*((x i).val : ZMod (p^k))⁻¹) else 0) =
      derivativeCarrySum p r k s b := by
  classical
  unfold derivativeCarrySum carrySum
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  change (if lowCondition p (p^r) b x then _ else _) =
    ∑ i, (s i:ZMod (p^k))*
      (if lowCondition p (p^r) b x then _ else _)
  by_cases hx : lowCondition p (p^r) b x
  · simp only [hx, ite_true, shifted_product]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · simp only [hx, ite_false, mul_zero, Finset.sum_const_zero]

/-- The concrete full carry lift, at exactly the source proof's precision. -/
theorem carrySum_double (p r d a : ℕ) (s : Fin d → ℕ)
    (hp : p.Prime) (hr : 1 ≤ r) (hd : 0 < d) (hdp : d+1 < p)
    (ha : 1 ≤ a) :
    carrySum p (r+1) (2*r+1) s a =
      (∑ b : Fin (d-1), (carryCount p d a (b.val+1) : ZMod (p^(2*r+1))) *
        carrySum p r (2*r+1) s (b.val+1)) -
      (p : ZMod (p^(2*r+1)))^r *
        ∑ b : Fin (d-1), (firstMoment p d a (b.val+1) ⟨0, hd⟩ : ZMod (p^(2*r+1))) *
          derivativeCarrySum p r (2*r+1) s (b.val+1) := by
  classical
  rw [carrySum_reindex p r (2*r+1) d a s hp.pos hr hd, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  have hb : 1 ≤ b.val+1 := by omega
  have hbd : b.val+1 < d := by have := b.isLt; omega
  rw [← product_derivative_sum]
  unfold carrySum
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  change (∑ y, if lowCondition p (p^r) (b.val+1) x ∧
    digitCondition p a (b.val+1) y then _ else _) =
    _ * (if lowCondition p (p^r) (b.val+1) x then _ else _) -
      _ * (_ * (if lowCondition p (p^r) (b.val+1) x then _ else _))
  by_cases hx : lowCondition p (p^r) (b.val+1) x
  · simp only [hx, true_and, ite_true]
    rw [← digitFiber_sum]
    have ht := concrete_lifted_fiber p r d a (b.val+1) s (fun i => (x i).val)
      ⟨0, hd⟩ hp hr hdp ha hb hbd (fun i => (hx.1 i).2)
    simp only [joinDigits_val]
    rw [ht]
    simp only [mul_assoc]
    rw [← Finset.mul_sum]
    ring
  · simp only [hx, false_and, ite_false, Finset.sum_const_zero, mul_zero, sub_self]

#print axioms shifted_product
#print axioms carrySum_double
end FiniteMT
```

### `Reduction.lean`

```lean
import Carry
import ModularTaylor
open scoped BigOperators
noncomputable section
namespace FiniteMT

theorem map_zmod_unit_inverse (m n : ℕ) (f : ZMod m →+* ZMod n) (u : (ZMod m)ˣ) :
    f ((u : ZMod m)⁻¹) = (f (u : ZMod m))⁻¹ := by
  rw [ZMod.inv_coe_unit]
  have he := ZMod.inv_coe_unit (Units.map f.toMonoidHom u)
  exact he.symm

theorem reduce_carrySum (p r k l : ℕ) {d : ℕ} (s : Fin d → ℕ) (a : ℕ)
    (hp : p.Prime) (hkl : k ≤ l) :
    ZMod.castHom (pow_dvd_pow p hkl) (ZMod (p^k)) (carrySum p r l s a) =
      carrySum p r k s a := by
  classical
  by_cases hl : l=0
  · have hk : k=0 := by omega
    subst l
    subst k
    let : Subsingleton (ZMod (p^0)) := ZMod.subsingleton_iff.mpr (pow_zero p)
    exact Subsingleton.elim _ _
  let f := ZMod.castHom (pow_dvd_pow p hkl) (ZMod (p^k))
  change f (carrySum p r l s a) = _
  unfold carrySum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : (∀ i, 0 < (x i).val ∧ ¬ p ∣ (x i).val) ∧
      (∑ i, (x i).val) = a*p^r
  · simp only [ite_eq_left hx, map_prod, map_pow]
    apply Finset.prod_congr rfl
    intro i _
    obtain ⟨u, hu⟩ := Taylor.coordinate_isUnit p l (x i).val
      hp (by omega) (hx.1 i).2
    rw [← hu, map_zmod_unit_inverse]
    rw [hu, map_natCast]
  · simp only [ite_eq_right hx, map_zero]

theorem reduce_sumMod (p r k l : ℕ) {d : ℕ} (s : Fin d → ℕ)
    (hp : p.Prime) (hkl : k ≤ l) :
    ZMod.castHom (pow_dvd_pow p hkl) (ZMod (p^k)) (sumMod p r l s) =
      sumMod p r k s := by
  rw [sumMod_eq_first, sumMod_eq_first]
  exact reduce_carrySum p r k l s 1 hp hkl

#print axioms reduce_sumMod
end FiniteMT
```

### `LowReflection.lean`

```lean
import CarryReindex
import Mathlib.Algebra.Group.Fin.Basic
open scoped BigOperators
noncomputable section
namespace FiniteMT

def reflectLow (N d : ℕ) : (Fin d → Fin N) ≃ (Fin d → Fin N) where
  toFun x i := -(x i)
  invFun x i := -(x i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

theorem reflectLow_val (N d : ℕ) (hN : 0 < N)
    (x : Fin d → Fin N) (i : Fin d) (hx : 0 < (x i).val) :
    ((reflectLow N d x) i).val = N-(x i).val := by
  let : NeZero N := ⟨by omega⟩
  change (-(x i)).val = _
  rw [Fin.val_neg, ite_eq_right]
  intro h
  have he := congrArg Fin.val h
  simp only [Fin.val_zero] at he
  omega

theorem reflectLow_good (p N d : ℕ) (hN : 0 < N) (hpN : p ∣ N)
    (x : Fin d → Fin N) :
    (∀ i, 0 < ((reflectLow N d x) i).val ∧ ¬ p ∣ ((reflectLow N d x) i).val) ↔
      (∀ i, 0 < (x i).val ∧ ¬ p ∣ (x i).val) := by
  let : NeZero N := ⟨by omega⟩
  have forward (x : Fin d → Fin N)
      (hx : ∀ i, 0 < (x i).val ∧ ¬ p ∣ (x i).val) :
      ∀ i, 0 < ((reflectLow N d x) i).val ∧ ¬ p ∣ ((reflectLow N d x) i).val := by
    intro i
    rw [reflectLow_val N d hN x i (hx i).1]
    have hxi := (x i).isLt
    refine ⟨by omega, ?_⟩
    intro h
    apply (hx i).2
    have he : N-(x i).val+(x i).val = N := Nat.sub_add_cancel hxi.le
    have hd : p ∣ (N-(x i).val)+(x i).val := by rw [he]; exact hpN
    exact (Nat.dvd_add_iff_right h).mpr hd
  constructor
  · intro hx
    have h := forward (reflectLow N d x) hx
    simpa only [reflectLow, Equiv.coe_fn_mk, neg_neg] using h
  · exact forward x

theorem reflectLow_total (N d : ℕ) (hN : 0 < N)
    (x : Fin d → Fin N) (hx : ∀ i, 0 < (x i).val) :
    (∑ i, ((reflectLow N d x) i).val)+(∑ i, (x i).val) = d*N := by
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ _i : Fin d, N := by
      apply Finset.sum_congr rfl
      intro i _
      rw [reflectLow_val N d hN x i (hx i), Nat.sub_add_cancel (x i).isLt.le]
    _ = _ := by simp

theorem lowCondition_reflect (p N d b : ℕ) (hN : 0 < N) (hpN : p ∣ N) (hb : b ≤ d)
    (x : Fin d → Fin N) :
    lowCondition p N (d-b) (reflectLow N d x) ↔ lowCondition p N b x := by
  unfold lowCondition
  rw [reflectLow_good p N d hN hpN]
  constructor
  · rintro ⟨hx, ht⟩
    refine ⟨hx, ?_⟩
    have hs := reflectLow_total N d hN x (fun i => (hx i).1)
    have hdb := Nat.sub_add_cancel hb
    nlinarith
  · rintro ⟨hx, ht⟩
    refine ⟨hx, ?_⟩
    have hs := reflectLow_total N d hN x (fun i => (hx i).1)
    have hdb := Nat.sub_add_cancel hb
    nlinarith

theorem carrySum_reflection_reindex (p r k d b : ℕ) (s : Fin d → ℕ)
    (hp : 0 < p) (hr : 1 ≤ r) (hb : b ≤ d) :
    carrySum p r k s (d-b) =
      ∑ x : Fin d → Fin (p^r), if lowCondition p (p^r) b x then
        ∏ i, (((reflectLow (p^r) d x i).val : ZMod (p^k))⁻¹)^s i else 0 := by
  unfold carrySum
  rw [← Equiv.sum_comp (reflectLow (p^r) d)]
  apply Finset.sum_congr rfl
  intro x _
  change (if lowCondition p (p^r) (d-b) (reflectLow (p^r) d x) then _ else _) = _
  simp only [lowCondition_reflect p (p^r) d b (pow_pos hp _) (dvd_pow_self p (by omega)) hb]

#print axioms carrySum_reflection_reindex
end FiniteMT
```

### `ReductionKernel.lean`

```lean
import Reduction
open scoped BigOperators
namespace FiniteMT

/-- Exact relation between vanishing after reduction and divisibility in any precision. -/
theorem reduction_zero_iff (p k l : ℕ) (hp : p.Prime) (hkl : k ≤ l)
    (x : ZMod (p^l)) :
    ZMod.castHom (pow_dvd_pow p hkl) (ZMod (p^k)) x = 0 ↔
      (p : ZMod (p^l))^k ∣ x := by
  let : NeZero (p^l) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let f := ZMod.castHom (pow_dvd_pow p hkl) (ZMod (p^k))
  change f x = 0 ↔ _
  constructor
  · intro hx
    have hval : (x.val : ZMod (p^k)) = 0 := by
      rw [← map_natCast f x.val, ZMod.natCast_zmod_val, hx]
    obtain ⟨q, hq⟩ := (ZMod.natCast_eq_zero_iff x.val (p^k)).mp hval
    refine ⟨(q : ZMod (p^l)), ?_⟩
    rw [← ZMod.natCast_zmod_val x, hq, Nat.cast_mul, Nat.cast_pow]
  · rintro ⟨q, rfl⟩
    rw [map_mul, map_pow, map_natCast, ZMod.natCast_pow_eq_zero_of_le p (le_refl k), zero_mul]

#print axioms reduction_zero_iff
end FiniteMT
```

### `ReflectionTaylor.lean`

```lean
import CarryFiber
import LowReflection
import DoubleLift
import Mathlib.Algebra.Ring.Units
open scoped BigOperators
noncomputable section
namespace FiniteMT

/-- First-order reflection expansion, valid in any ZMod with h²=0. -/
theorem reflection_product (m d : ℕ) (u : Fin d → (ZMod m)ˣ) (s : Fin d → ℕ)
    (h : ZMod m) (hh : h^2=0) :
    (∏ i, ((h-(u i:ZMod m))⁻¹)^s i) =
      (-1 : ZMod m)^(weight s) *
        ((∏ i, (↑(u i)⁻¹:ZMod m)^s i) +
          h*((∏ i, (↑(u i)⁻¹:ZMod m)^s i)*
            ∑ i, (s i:ZMod m)*(↑(u i)⁻¹:ZMod m))) := by
  have hh3 : h^3=0 := by rw [show (3:ℕ)=2+1 from rfl, pow_succ, hh, zero_mul]
  have ht := Taylor.finite_product_inverse_lift m d (fun i => -(u i)) h (fun _ => 1) s hh3
  have hv (i : Fin d) : (↑(-(u i))⁻¹:ZMod m) = -(↑(u i)⁻¹:ZMod m) := rfl
  have hb : (∏ i, (↑(-(u i))⁻¹:ZMod m)^s i) =
      (-1:ZMod m)^weight s*(∏ i, (↑(u i)⁻¹:ZMod m)^s i) := by
    have he (i : Fin d) : (-(↑(u i)⁻¹:ZMod m))^s i =
        (-1:ZMod m)^s i*(↑(u i)⁻¹:ZMod m)^s i := by
      rw [← neg_one_mul, mul_pow]
    simp only [hv, he, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, weight]
  have hl : Taylor.linear (List.ofFn fun i => Taylor.coeff (-(u i), (1:ZMod m), s i)) =
      ∑ i, (s i:ZMod m)*(↑(u i)⁻¹:ZMod m) := by
    rw [linear_eq_sum]
    simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def, Taylor.coeff, hv]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hb, hl, hh, zero_mul, add_zero] at ht
  simp only [Units.val_neg, mul_one] at ht
  simp only [sub_eq_add_neg, add_comm h]
  rw [ht]
  ring

/-- The actual low-coordinate reflection, with the derivative term retained. -/
theorem carrySum_reflection (p r d b : ℕ) (s : Fin d → ℕ)
    (hp : p.Prime) (hr : 1 ≤ r) (hb : b ≤ d) :
    carrySum p r (2*r) s (d-b) =
      (-1 : ZMod (p^(2*r)))^weight s *
        (carrySum p r (2*r) s b +
          (p : ZMod (p^(2*r)))^r*derivativeCarrySum p r (2*r) s b) := by
  classical
  rw [carrySum_reflection_reindex p r (2*r) d b s hp.pos hr hb,
    ← product_derivative_sum]
  unfold carrySum
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  change (if lowCondition p (p^r) b x then _ else _) =
    _ * ((if lowCondition p (p^r) b x then _ else _) +
      _ * (if lowCondition p (p^r) b x then _ else _))
  by_cases hx : lowCondition p (p^r) b x
  · simp only [hx, ite_true]
    obtain ⟨u, hu⟩ : ∃ u : Fin d → (ZMod (p^(2*r)))ˣ,
        ∀ i, (u i : ZMod (p^(2*r))) = ((x i).val : ZMod (p^(2*r))) := by
      choose u hu using fun i => Taylor.coordinate_isUnit p (2*r) (x i).val hp
        (by omega) (hx.1 i).2
      exact ⟨u, hu⟩
    have he (i : Fin d) :
        (((reflectLow (p^r) d x i).val : ZMod (p^(2*r)))) =
          (p : ZMod (p^(2*r)))^r - (u i : ZMod (p^(2*r))) := by
      rw [reflectLow_val (p^r) d (pow_pos hp.pos _) x i (hx.1 i).1,
        Nat.cast_sub (x i).isLt.le, Nat.cast_pow, hu]
    simp_rw [he]
    have hh : ((p : ZMod (p^(2*r)))^r)^2 = 0 := by
      rw [← pow_mul]
      exact ZMod.natCast_pow_eq_zero_of_le p (by omega)
    rw [reflection_product _ d u s _ hh]
    have hvinv (i : Fin d) : (↑(u i)⁻¹ : ZMod (p^(2*r))) =
        ((x i).val : ZMod (p^(2*r)))⁻¹ := by
      rw [← ZMod.inv_coe_unit, hu]
    simp only [hvinv]
    rw [Finset.mul_sum]
  · simp only [hx, ite_false, mul_zero, add_zero]

#print axioms reflection_product
#print axioms carrySum_reflection
end FiniteMT
```

### `ReductionDouble.lean`

```lean
import DoubleLift
import ReductionKernel
open scoped BigOperators
namespace FiniteMT

theorem reduce_derivativeCarrySum (p r k l : ℕ) {d : ℕ} (s : Fin d → ℕ) (b : ℕ)
    (hp : p.Prime) (hkl : k ≤ l) :
    ZMod.castHom (pow_dvd_pow p hkl) (ZMod (p^k)) (derivativeCarrySum p r l s b) =
      derivativeCarrySum p r k s b := by
  unfold derivativeCarrySum
  simp only [map_sum, map_mul, map_natCast, reduce_carrySum p r k l _ b hp hkl]

theorem carrySum_double_at (p r k d a : ℕ) (s : Fin d → ℕ)
    (hp : p.Prime) (hr : 1 ≤ r) (hd : 0 < d) (hdp : d+1 < p)
    (ha : 1 ≤ a) (hk : k ≤ 2*r+1) :
    carrySum p (r+1) k s a =
      (∑ b : Fin (d-1), (carryCount p d a (b.val+1) : ZMod (p^k)) *
        carrySum p r k s (b.val+1)) -
      (p : ZMod (p^k))^r *
        ∑ b : Fin (d-1), (firstMoment p d a (b.val+1) ⟨0, hd⟩ : ZMod (p^k)) *
          derivativeCarrySum p r k s (b.val+1) := by
  have ht := congrArg (ZMod.castHom (pow_dvd_pow p hk) (ZMod (p^k)))
    (carrySum_double p r d a s hp hr hd hdp ha)
  simpa only [map_sub, map_sum, map_mul, map_pow, map_natCast,
    reduce_carrySum p _ k (2*r+1) _ _ hp hk,
    reduce_derivativeCarrySum p r k (2*r+1) _ _ hp hk] using ht

theorem derivativeCarrySum_dvd (p r k d b : ℕ) (s : Fin d → ℕ)
    (hp : p.Prime) (hr : 1 ≤ r) (hdp : d+1 < p) (hb : 1 ≤ b) (hbd : b < d) :
    (p : ZMod (p^k))^(r-1) ∣ derivativeCarrySum p r k s b := by
  apply Finset.dvd_sum
  intro i _
  exact dvd_mul_of_dvd_right
    (weak_divisibility_of_carry p d k (countTheorem p d hp hdp)
      (weakCarryRecurrence p d k hp) r hr (shiftExponent s i) b hb hbd) _

/-- Source proof equation (8), obtained without a circular induction. -/
theorem carrySum_weak_plus (p r d a : ℕ) (s : Fin d → ℕ)
    (hp : p.Prime) (hr : 1 ≤ r) (hd : 0 < d) (hdp : d+1 < p)
    (ha : 1 ≤ a) :
    carrySum p (r+1) (r+1) s a =
      ∑ b : Fin (d-1), (carryCount p d a (b.val+1) : ZMod (p^(r+1))) *
        carrySum p r (r+1) s (b.val+1) := by
  rw [carrySum_double_at p r (r+1) d a s hp hr hd hdp ha (by omega)]
  have he : (p : ZMod (p^(r+1)))^r *
      ∑ b : Fin (d-1), (firstMoment p d a (b.val+1) ⟨0, hd⟩ : ZMod (p^(r+1))) *
        derivativeCarrySum p r (r+1) s (b.val+1) = 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro b _
    have hb : b.val+1 < d := by have := b.isLt; omega
    obtain ⟨c, hc⟩ := firstMoment_dvd p d a (b.val+1) ⟨0, hd⟩ hp hdp ha (by omega) hb
    obtain ⟨q, hq⟩ := derivativeCarrySum_dvd p r (r+1) d (b.val+1) s hp hr hdp (by omega) hb
    rw [hc, Nat.cast_mul, hq]
    calc
      _ = (p : ZMod (p^(r+1)))^(2*r)*(c:ZMod (p^(r+1)))*q := by
        have hex : 2*r = r+1+(r-1) := by omega
        simp only [hex, pow_add, pow_one]
        ring
      _ = 0 := by
        rw [ZMod.natCast_pow_eq_zero_of_le p (by omega), zero_mul, zero_mul]
  rw [he, sub_zero]

#print axioms carrySum_double_at
#print axioms carrySum_weak_plus
end FiniteMT
```

### `ParityBound.lean`

```lean
import ReflectionTaylor
import ReductionDouble
open scoped BigOperators
namespace FiniteMT

theorem sign_square {R : Type*} [CommRing R] (w : ℕ) :
    (-1:R)^w*(-1:R)^w = 1 := by
  rw [← pow_two, ← pow_mul, Nat.mul_comm w 2, pow_mul, neg_one_sq, one_pow]

theorem carrySum_reflection_at (p r k d b : ℕ) (s : Fin d → ℕ)
    (hp : p.Prime) (hr : 1 ≤ r) (hb : b ≤ d) (hk : k ≤ 2*r) :
    carrySum p r k s (d-b) =
      (-1 : ZMod (p^k))^weight s *
        (carrySum p r k s b + (p : ZMod (p^k))^r*derivativeCarrySum p r k s b) := by
  have ht := congrArg (ZMod.castHom (pow_dvd_pow p hk) (ZMod (p^k)))
    (carrySum_reflection p r d b s hp hr hb)
  simpa only [map_add, map_mul, map_pow, map_neg, map_one, map_natCast,
    reduce_carrySum p r k (2*r) _ _ hp hk,
    reduce_derivativeCarrySum p r k (2*r) _ _ hp hk] using ht

/-- The sign-reflection identity after its derivative term vanishes. -/
theorem carrySum_parity_at (p r d b : ℕ) (s : Fin d → ℕ)
    (hp : p.Prime) (hr : 1 ≤ r) (hdp : d+1 < p)
    (hb : 1 ≤ b) (hbd : b < d) :
    carrySum p r (2*r-1) s (d-b) =
      (-1 : ZMod (p^(2*r-1)))^weight s * carrySum p r (2*r-1) s b := by
  rw [carrySum_reflection_at p r (2*r-1) d b s hp hr (by omega) (by omega)]
  obtain ⟨q, hq⟩ := derivativeCarrySum_dvd p r (2*r-1) d b s hp hr hdp hb hbd
  have he : (p : ZMod (p^(2*r-1)))^r * derivativeCarrySum p r (2*r-1) s b = 0 := by
    rw [hq, ← mul_assoc, ← pow_add]
    have hpow : r+(r-1) = 2*r-1 := by omega
    rw [hpow, ZMod.natCast_pow_eq_zero_of_le p (by omega), zero_mul]
  rw [he, add_zero]

theorem carrySum_parity_difference (p r d b : ℕ) (s : Fin d → ℕ)
    (hp : p.Prime) (hr : 1 ≤ r) (hdp : d+1 < p)
    (hb : 1 ≤ b) (hbd : b < d) :
    carrySum p r (2*r-1) s b -
      (-1 : ZMod (p^(2*r-1)))^weight s * carrySum p r (2*r-1) s (d-b) = 0 := by
  rw [carrySum_parity_at p r d b s hp hr hdp hb hbd, ← mul_assoc, sign_square, one_mul, sub_self]

/-- Wrong-parity divisibility in every ambient precision. -/
theorem wrongParity_dvd (p r k d b : ℕ) (s : Fin d → ℕ)
    (hp : p.Prime) (hr : 1 ≤ r) (hdp : d+1 < p)
    (hb : 1 ≤ b) (hbd : b < d) :
    (p : ZMod (p^k))^(2*r-1) ∣
      carrySum p r k s b - (-1 : ZMod (p^k))^weight s * carrySum p r k s (d-b) := by
  by_cases hk : 2*r-1 ≤ k
  · apply (reduction_zero_iff p (2*r-1) k hp hk _).mp
    simpa only [map_sub, map_mul, map_pow, map_neg, map_one,
      reduce_carrySum p r (2*r-1) k _ _ hp hk] using
        carrySum_parity_difference p r d b s hp hr hdp hb hbd
  · have hkle : k ≤ 2*r-1 := by omega
    have ht := congrArg (ZMod.castHom (pow_dvd_pow p hkle) (ZMod (p^k)))
      (carrySum_parity_difference p r d b s hp hr hdp hb hbd)
    have he : carrySum p r k s b -
        (-1 : ZMod (p^k))^weight s * carrySum p r k s (d-b) = 0 := by
      simpa only [map_sub, map_mul, map_pow, map_neg, map_one, map_zero,
        reduce_carrySum p r k (2*r-1) _ _ hp hkle] using ht
    rw [he]
    exact dvd_zero _

/-- Pointwise reflection projection, avoiding an artificial field structure. -/
def carryProject (p r k : ℕ) {d : ℕ} (s : Fin d → ℕ)
    (eta : ZMod (p^k)) (b : ℕ) : ZMod (p^k) :=
  (2 : ZMod (p^k))⁻¹*(carrySum p r k s b+eta*carrySum p r k s (d-b))

theorem wrongParity_project_dvd (p r k d b : ℕ) (s : Fin d → ℕ)
    (hp : p.Prime) (hr : 1 ≤ r) (hdp : d+1 < p)
    (hb : 1 ≤ b) (hbd : b < d) :
    (p : ZMod (p^k))^(2*r-1) ∣
      carrySum p r k s b - carryProject p r k s ((-1)^weight s) b := by
  have htwo : (2:ZMod (p^k))⁻¹*2=1 := by
    by_cases hk : k=0
    · subst k
      let : Subsingleton (ZMod (p^0)) := ZMod.subsingleton_iff.mpr (pow_zero p)
      exact Subsingleton.elim _ _
    · apply ZMod.inv_mul_of_unit
      exact Taylor.coordinate_isUnit p k 2 hp (by omega)
        (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  have he : carrySum p r k s b - carryProject p r k s ((-1)^weight s) b =
      (2:ZMod (p^k))⁻¹*(carrySum p r k s b -
        (-1:ZMod (p^k))^weight s*carrySum p r k s (d-b)) := by
    unfold carryProject
    calc
      _ = (2:ZMod (p^k))⁻¹*2*carrySum p r k s b -
          (2:ZMod (p^k))⁻¹*(carrySum p r k s b+
            (-1:ZMod (p^k))^weight s*carrySum p r k s (d-b)) := by rw [htwo, one_mul]
      _ = _ := by ring
  rw [he]
  exact dvd_mul_of_dvd_right (wrongParity_dvd p r k d b s hp hr hdp hb hbd) _

#print axioms wrongParity_dvd
#print axioms wrongParity_project_dvd
end FiniteMT
```

### `ShiftedParity.lean`

```lean
import ParityBound
open scoped BigOperators
namespace FiniteMT

theorem weight_shift {d : ℕ} (s : Fin d → ℕ) (i : Fin d) :
    weight (shiftExponent s i) = weight s+1 := by
  classical
  unfold weight shiftExponent
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [← Finset.add_sum_erase _ s (Finset.mem_univ i)]
  simp only [Finset.sdiff_singleton_eq_erase]
  omega

/-- Source proof (10), before multiplying by the inverse of 2. -/
theorem shiftedParity_dvd (p r k d b : ℕ) (s : Fin d → ℕ)
    (hp : p.Prime) (hr : 1 ≤ r) (hdp : d+1 < p)
    (hb : 1 ≤ b) (hbd : b < d) :
    (p : ZMod (p^k))^(2*r-1) ∣
      derivativeCarrySum p r k s b +
        (-1:ZMod (p^k))^weight s * derivativeCarrySum p r k s (d-b) := by
  unfold derivativeCarrySum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.dvd_sum
  intro i _
  have hd := wrongParity_dvd p r k d b (shiftExponent s i) hp hr hdp hb hbd
  rw [weight_shift, pow_succ, mul_neg_one, neg_mul, sub_neg_eq_add] at hd
  have he : (s i:ZMod (p^k))*carrySum p r k (shiftExponent s i) b +
      (-1:ZMod (p^k))^weight s*((s i:ZMod (p^k))*carrySum p r k (shiftExponent s i) (d-b)) =
      (s i:ZMod (p^k))*(carrySum p r k (shiftExponent s i) b +
        (-1:ZMod (p^k))^weight s*carrySum p r k (shiftExponent s i) (d-b)) := by ring
  rw [he]
  exact dvd_mul_of_dvd_right hd _

theorem shiftedParity_project_dvd (p r k d b : ℕ) (s : Fin d → ℕ)
    (hp : p.Prime) (hr : 1 ≤ r) (hdp : d+1 < p)
    (hb : 1 ≤ b) (hbd : b < d) :
    (p : ZMod (p^k))^(2*r-1) ∣
      (2:ZMod (p^k))⁻¹*(derivativeCarrySum p r k s b +
        (-1:ZMod (p^k))^weight s * derivativeCarrySum p r k s (d-b)) :=
  dvd_mul_of_dvd_right (shiftedParity_dvd p r k d b s hp hr hdp hb hbd) _

#print axioms weight_shift
#print axioms shiftedParity_project_dvd
end FiniteMT
```

### `CountGenerating.lean`

```lean
import CountPolynomial
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.LinearCombination
open scoped BigOperators
open Polynomial
noncomputable section
namespace FiniteMT

def digitPolynomial (R : Type*) [Semiring R] (p : ℕ) : R[X] :=
  ∑ t : Fin p, X^t.val

theorem digitPolynomial_power (R : Type*) [CommSemiring R] (p d : ℕ) :
    (digitPolynomial R p)^d = ∑ y : Fin d → Fin p, X^(∑ i, (y i).val) := by
  classical
  calc
    _ = ∏ _i : Fin d, digitPolynomial R p := by simp
    _ = ∑ y : Fin d → Fin p, ∏ i, (X : R[X])^(y i).val := by
      simp only [digitPolynomial]
      rw [Fintype.prod_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.prod_pow_eq_pow_sum]

theorem count_coefficient (R : Type*) [CommSemiring R] (p d a b : ℕ)
    (hb : b ≤ a*p) :
    (carryCount p d a b : R) = ((digitPolynomial R p)^d).coeff (a*p-b) := by
  classical
  rw [digitPolynomial_power, finsetSum_coeff]
  simp only [carryCount, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro y _
  have he : digitCondition p a b y ↔ a*p-b = ∑ i, (y i).val := by
    dsimp [digitCondition]; omega
  simp only [coeff_X_pow, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, he]

theorem digitPolynomial_geom (R : Type*) [CommRing R] (p : ℕ) :
    (1-X : R[X])*digitPolynomial R p = 1-X^p := by
  unfold digitPolynomial
  rw [Fin.sum_univ_eq_sum_range]
  exact mul_neg_geom_sum X p

theorem digitPolynomial_derivative_relation (R : Type*) [CommRing R] (p : ℕ) :
    (1-X : R[X])*derivative (digitPolynomial R p) =
      digitPolynomial R p - C (p:R)*X^(p-1) := by
  have h := congrArg derivative (digitPolynomial_geom R p)
  simp only [derivative_mul, derivative_sub, derivative_one, derivative_X,
    derivative_X_pow, zero_sub] at h
  linear_combination h

theorem countPolynomial_differential (R : Type*) [CommRing R] (p d : ℕ) (hd : 1 ≤ d) :
    (1-X : R[X])*derivative ((digitPolynomial R p)^d) =
      C (d:R)*(digitPolynomial R p)^d -
        C ((d:R)*(p:R))*X^(p-1)*(digitPolynomial R p)^(d-1) := by
  rw [derivative_pow]
  have hpow : (digitPolynomial R p)^(d-1)*(digitPolynomial R p) =
      (digitPolynomial R p)^d := by
    rw [← pow_succ, Nat.sub_add_cancel hd]
  calc
    _ = C (d:R)*(digitPolynomial R p)^(d-1)*
        ((1-X)*derivative (digitPolynomial R p)) := by ring
    _ = _ := by rw [digitPolynomial_derivative_relation, ← hpow, map_mul]; ring

/-- The coefficient recurrence before reducing modulo p². -/
theorem countPolynomial_coeff_recurrence (R : Type*) [CommRing R] (p d n : ℕ) (hd : 1 ≤ d) :
    ((n+1:R))*((digitPolynomial R p)^d).coeff (n+1) -
      ((n+d:R))*((digitPolynomial R p)^d).coeff n =
      -((d:R)*(p:R))*((X^(p-1)*(digitPolynomial R p)^(d-1)).coeff n) := by
  have ht := congrArg (fun f : R[X] => f.coeff n) (countPolynomial_differential R p d hd)
  rw [sub_mul, one_mul] at ht
  have hX (f : R[X]) (n : ℕ) : (X*derivative f).coeff n = (n:R)*f.coeff n := by
    cases n with
    | zero => simp
    | succ n => rw [coeff_X_mul, coeff_derivative]; push_cast; ring
  simp only [coeff_sub, coeff_derivative, hX, mul_assoc, coeff_C_mul] at ht
  linear_combination ht

#print axioms countPolynomial_coeff_recurrence
end FiniteMT
```

### `CountRecurrence.lean`

```lean
import CountGenerating
open scoped BigOperators
open Polynomial
noncomputable section
namespace FiniteMT

theorem p_cast_multiple_zero (p m : ℕ) (hm : p ∣ m) :
    (p : ZMod (p^2))*(m : ZMod (p^2)) = 0 := by
  obtain ⟨q, rfl⟩ := hm
  rw [Nat.cast_mul, ← mul_assoc, ← pow_two,
    ZMod.natCast_pow_eq_zero_of_le p (le_refl 2), zero_mul]

/-- A differential alternative to inclusion-exclusion for the p-linear carry row. -/
theorem carryCount_row_recurrence (p d a b : ℕ) (hp : p.Prime) (hdp : d+1 < p)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hbd : b+1 < d) :
    (b : ZMod (p^2))*(carryCount p d a b : ZMod (p^2)) +
      ((d-1-b : ℕ) : ZMod (p^2))*(carryCount p d a (b+1) : ZMod (p^2)) = 0 := by
  let A := ZMod (p^2)
  let n := a*p-b-1
  have hap : p ≤ a*p := by simpa using Nat.mul_le_mul_right p ha
  have hab : b+1 ≤ a*p := by omega
  have hn1 : n+1 = a*p-b := by dsimp [n]; omega
  have hn0 : n = a*p-(b+1) := by dsimp [n]; omega
  have ht := countPolynomial_coeff_recurrence A p d n (by omega)
  rw [hn1, hn0, ← count_coefficient A p d a b (by omega),
    ← count_coefficient A p d a (b+1) hab] at ht
  have herr : (d:A)*(p:A)*
      ((X^(p-1)*(digitPolynomial A p)^(d-1)).coeff (a*p-(b+1))) = 0 := by
    rw [coeff_X_pow_mul']
    split_ifs with hcut
    · have ha2 : 2 ≤ a := by
        have hp1 := hp.one_le
        by_contra h
        have hae : a=1 := by omega
        subst a
        simp only [one_mul] at hcut
        omega
      have he : a*p-(b+1)-(p-1) = (a-1)*p-b := by
        have ha1 := Nat.sub_add_cancel ha
        have hp1 := Nat.sub_add_cancel hp.one_le
        have hc : b+p ≤ a*p := by
          have hmul : 2*p ≤ a*p := Nat.mul_le_mul_right p ha2
          omega
        have h1 := Nat.sub_add_cancel hab
        have h2 := Nat.sub_add_cancel hcut
        have hlow : b ≤ (a-1)*p := by
          have : p ≤ (a-1)*p := by simpa using Nat.mul_le_mul_right p (by omega : 1 ≤ a-1)
          omega
        have h3 := Nat.sub_add_cancel hlow
        nlinarith
      rw [he, ← count_coefficient A p (d-1) (a-1) b (by
        have : p ≤ (a-1)*p := by
          simpa using Nat.mul_le_mul_right p (by omega : 1 ≤ a-1)
        omega)]
      have hz := p_cast_multiple_zero p (carryCount p (d-1) (a-1) b)
        (carryCount_dvd p (d-1) (a-1) b hp (by omega) (by omega) hb (by omega))
      change (d:A)*(p:A)*(carryCount p (d-1) (a-1) b:A) = 0
      rw [mul_assoc, hz, mul_zero]
    · rw [mul_zero]
  have ht' : ((n:A)+1)*(carryCount p d a b:A) -
      ((n+d:A))*(carryCount p d a (b+1):A) = 0 := by
    have herr' : -((d:A)*(p:A))*
        ((X^(p-1)*(digitPolynomial A p)^(d-1)).coeff (a*p-(b+1))) = 0 := by
      rw [neg_mul, herr, neg_zero]
    simpa only [hn1, hn0, herr'] using ht
  have hnat1 : n+1+b = a*p := by dsimp [n]; omega
  have hnat2 : n+d = a*p+(d-1-b) := by dsimp [n]; omega
  have h1 : (n:A)+1+(b:A) = (a:A)*(p:A) := by
    simpa only [A, Nat.cast_add, Nat.cast_one, Nat.cast_mul] using congrArg (fun t : ℕ => (t:A)) hnat1
  have h2 : ((n+d:A)) = (a:A)*(p:A)+((d-1-b:ℕ):A) := by
    simpa only [A, Nat.cast_add, Nat.cast_mul] using congrArg (fun t : ℕ => (t:A)) hnat2
  have hz1 := p_cast_multiple_zero p (carryCount p d a b)
    (carryCount_dvd p d a b hp hdp ha hb (by omega))
  have hz2 := p_cast_multiple_zero p (carryCount p d a (b+1))
    (carryCount_dvd p d a (b+1) hp hdp ha (by omega) hbd)
  change (b:A)*(carryCount p d a b:A) +
      ((d-1-b:ℕ):A)*(carryCount p d a (b+1):A) = 0
  linear_combination h1*(carryCount p d a b:A) - ht' -
    h2*(carryCount p d a (b+1):A) + (a:A)*hz1 - (a:A)*hz2

#print axioms carryCount_row_recurrence
end FiniteMT
```

### `RowKernel.lean`

```lean
import ParityBound
import Mathlib.Data.Nat.Choose.Basic
namespace FiniteMT

theorem row_normalized {R : Type*} [CommRing R] (n : ℕ) (v : ℕ → R)
    (hstep : ∀ i, i < n → ((i+1:ℕ):R)*v i+((n-i:ℕ):R)*v (i+1)=0)
    (hunit : ∀ i, i < n → IsUnit ((i+1:ℕ):R)) :
    ∀ i, i ≤ n → (n.choose i:R)*v i = (-1:R)^i*v 0 := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    intro hi
    have hin : i < n := by omega
    have hrel : ((n-i:ℕ):R)*v (i+1) = -((i+1:ℕ):R)*v i := by
      linear_combination hstep i hin
    have hc : ((i+1:ℕ):R)*(n.choose (i+1):R) =
        ((n-i:ℕ):R)*(n.choose i:R) := by
      have h := Nat.choose_succ_right_eq n i
      simpa only [Nat.cast_mul, mul_comm] using congrArg (fun t : ℕ => (t:R)) h
    apply (hunit i hin).mul_left_cancel
    calc
      _ = (n.choose i:R)*(((n-i:ℕ):R)*v (i+1)) := by rw [← mul_assoc, hc]; ring
      _ = ((i+1:ℕ):R)*(-((n.choose i:R)*v i)) := by rw [hrel]; ring
      _ = _ := by rw [ih (by omega), pow_succ]; ring

theorem row_reversal {R : Type*} [CommRing R] (n : ℕ) (v : ℕ → R)
    (hstep : ∀ i, i < n → ((i+1:ℕ):R)*v i+((n-i:ℕ):R)*v (i+1)=0)
    (hunit : ∀ i, i < n → IsUnit ((i+1:ℕ):R))
    (hcunit : ∀ i, i ≤ n → IsUnit (n.choose i:R)) (i : ℕ) (hi : i ≤ n) :
    v (n-i) = (-1:R)^n*v i := by
  have hleft := row_normalized n v hstep hunit (n-i) (Nat.sub_le _ _)
  have hright := row_normalized n v hstep hunit i hi
  rw [Nat.choose_symm hi] at hleft
  have hsign : (-1:R)^(n-i) = (-1:R)^n*(-1:R)^i := by
    calc
      _ = (-1:R)^(n-i)*((-1:R)^i*(-1:R)^i) := by rw [sign_square, mul_one]
      _ = _ := by rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hi]
  apply (hcunit i hi).mul_left_cancel
  rw [hleft, hsign]
  calc
    _ = (-1:R)^n*((n.choose i:R)*v i) := by rw [hright]; ring
    _ = _ := by ring


#print axioms row_reversal
end FiniteMT
```

### `RowSymmetry.lean`

```lean
import CountRecurrence
import RowKernel
import Mathlib.Data.Nat.Prime.Factorial
open scoped BigOperators
noncomputable section
namespace FiniteMT

theorem choose_isUnit_mod_prime_square (p n i : ℕ) (hp : p.Prime)
    (hn : n < p) (hi : i ≤ n) : IsUnit (n.choose i : ZMod (p^2)) := by
  apply Taylor.coordinate_isUnit p 2 (n.choose i) hp (by decide)
  intro hchoose
  have hfact : p ∣ n.factorial := by
    rw [← Nat.choose_mul_factorial_mul_factorial hi]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hchoose _) _
  have := hp.dvd_factorial.mp hfact
  omega

/-- Each row has the required opposite column parity modulo p². -/
theorem carryCount_column_parity (p d a b : ℕ) (hp : p.Prime) (hdp : d+1 < p)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hbd : b < d) :
    (carryCount p d a (d-b) : ZMod (p^2)) =
      (-1 : ZMod (p^2))^d*(carryCount p d a b : ZMod (p^2)) := by
  let A := ZMod (p^2)
  let n := d-2
  let v : ℕ → A := fun i => (carryCount p d a (i+1):A)
  have hd : 2 ≤ d := by omega
  have hs (i : ℕ) (hi : i < n) :
      ((i+1:ℕ):A)*v i+((n-i:ℕ):A)*v (i+1)=0 := by
    have ht := carryCount_row_recurrence p d a (i+1) hp hdp ha (by omega) (by dsimp [n] at hi; omega)
    have he : d-1-(i+1)=n-i := by dsimp [n]; omega
    simpa only [he] using ht
  have hu (i : ℕ) (hi : i < n) : IsUnit ((i+1:ℕ):A) := by
    apply Taylor.coordinate_isUnit p 2 (i+1) hp (by decide)
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by dsimp [n] at hi; omega)
  have hc (i : ℕ) (hi : i ≤ n) : IsUnit (n.choose i:A) :=
    choose_isUnit_mod_prime_square p n i hp (by dsimp [n]; omega) hi
  have ht := row_reversal n v hs hu hc (b-1) (by dsimp [n]; omega)
  have hb1 : b-1+1=b := Nat.sub_add_cancel hb
  have he : n-(b-1)+1=d-b := by dsimp [n]; omega
  have hsign : (-1:A)^n = (-1:A)^d := by
    have he : d=n+2 := by dsimp [n]; omega
    conv_rhs => rw [he, pow_add, neg_one_sq, mul_one]
  simpa only [v, he, hb1, hsign] using ht

#print axioms carryCount_column_parity
end FiniteMT
```

### `ProjectedCount.lean`

```lean
import RowSymmetry
import ReductionKernel
import Mathlib.Data.Fin.Rev
open scoped BigOperators
noncomputable section
namespace FiniteMT

def parityProjection {R : Type*} [CommRing R] {n : ℕ}
    (half eta : R) (v : Fin n → R) : Fin n → R :=
  fun b => half*(v b+eta*v b.rev)

def carryAction (p d k : ℕ) (v : Fin (d-1) → ZMod (p^k)) (a : ℕ) : ZMod (p^k) :=
  ∑ b, (carryCount p d a (b.val+1) : ZMod (p^k))*v b

theorem sum_reflection_cancel {R : Type*} [CommRing R] {n : ℕ}
    (m v : Fin n → R) (eta sign : R)
    (hm : ∀ b, m b.rev=sign*m b) (hsign : 1+eta*sign=0) :
    (∑ b, m b*(v b+eta*v b.rev)) = 0 := by
  simp only [mul_add, Finset.sum_add_distrib]
  have he : (∑ b, m b*(eta*v b.rev)) = ∑ b, sign*m b*(eta*v b) := by
    rw [← Equiv.sum_comp Fin.revPerm]
    simp only [Fin.revPerm_apply, Fin.rev_rev, hm]
  rw [he, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro b _
  calc
    _ = (1+eta*sign)*m b*v b := by ring
    _ = 0 := by rw [hsign, zero_mul, zero_mul]

theorem carryCount_column_parity_at (p d k a b : ℕ) (hp : p.Prime) (hdp : d+1 < p)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hbd : b < d) (hk : k ≤ 2) :
    (carryCount p d a (d-b) : ZMod (p^k)) =
      (-1 : ZMod (p^k))^d*(carryCount p d a b : ZMod (p^k)) := by
  have ht := congrArg (ZMod.castHom (pow_dvd_pow p hk) (ZMod (p^k)))
    (carryCount_column_parity p d a b hp hdp ha hb hbd)
  simpa only [map_mul, map_pow, map_neg, map_one, map_natCast] using ht

theorem projected_count_zero (p d k a : ℕ) (v : Fin (d-1) → ZMod (p^k))
    (hp : p.Prime) (hdp : d+1 < p) (ha : 1 ≤ a) (hk : k ≤ 2) :
    (∑ b : Fin (d-1), (carryCount p d a (b.val+1):ZMod (p^k))*
      (v b+(-1:ZMod (p^k))^(d+1)*v b.rev)) = 0 := by
  apply sum_reflection_cancel _ v ((-1)^(d+1)) ((-1)^d)
  · intro b
    have hbd : b.val+1 < d := by have := b.isLt; omega
    have he : b.rev.val+1 = d-(b.val+1) := by rw [Fin.val_rev]; omega
    simp only [he]
    exact carryCount_column_parity_at p d k a (b.val+1) hp hdp ha (by omega) hbd hk
  · rw [pow_succ]
    calc
      _ = 1-((-1:ZMod (p^k))^d*(-1:ZMod (p^k))^d) := by ring
      _ = 0 := by rw [sign_square, sub_self]

/-- Source proof (4), uniform in every ambient precision and test vector. -/
theorem projected_count_dvd (p d k a : ℕ) (v : Fin (d-1) → ZMod (p^k))
    (hp : p.Prime) (hdp : d+1 < p) (ha : 1 ≤ a) :
    (p:ZMod (p^k))^2 ∣
      carryAction p d k
        (parityProjection (2:ZMod (p^k))⁻¹ ((-1)^(d+1)) v) a := by
  have hraw : (p:ZMod (p^k))^2 ∣
      ∑ b : Fin (d-1), (carryCount p d a (b.val+1):ZMod (p^k))*
        (v b+(-1:ZMod (p^k))^(d+1)*v b.rev) := by
    by_cases hk : 2 ≤ k
    · apply (reduction_zero_iff p 2 k hp hk _).mp
      simpa only [map_sum, map_mul, map_add, map_natCast, map_pow, map_neg, map_one]
        using projected_count_zero p d 2 a
          (fun b => ZMod.castHom (pow_dvd_pow p hk) (ZMod (p^2)) (v b)) hp hdp ha (le_refl 2)
    · rw [projected_count_zero p d k a v hp hdp ha (by omega)]
      exact dvd_zero _
  have he : carryAction p d k
        (parityProjection (2:ZMod (p^k))⁻¹ ((-1)^(d+1)) v) a =
      (2:ZMod (p^k))⁻¹ *
        ∑ b : Fin (d-1), (carryCount p d a (b.val+1):ZMod (p^k))*
          (v b+(-1:ZMod (p^k))^(d+1)*v b.rev) := by
    unfold carryAction parityProjection
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [he]
  exact dvd_mul_of_dvd_right hraw _

#print axioms projected_count_dvd
end FiniteMT
```

### `ScalarScaling.lean`

```lean
import ReductionKernel
open scoped BigOperators
namespace FiniteMT

/-- One scalar recurrence interface for all three exceptional scaling clauses. -/
def ScalarCarryRecurrence (p d e : ℕ) (s : Fin d → ℕ) : Prop :=
  ∀ r, 1 ≤ r → ∀ k a, 1 ≤ a → a < d →
    (p : ZMod (p^k))^(e*r+1) ∣
      carrySum p (r+1) k s a-(p : ZMod (p^k))^e*carrySum p r k s a

theorem scalar_scaling_dvd (p d e : ℕ) (s : Fin d → ℕ)
    (hrec : ScalarCarryRecurrence p d e s) :
    ∀ r, 1 ≤ r → ∀ k a, 1 ≤ a → a < d →
      (p : ZMod (p^k))^(e*(r-1)+1) ∣
        carrySum p r k s a -
          (p : ZMod (p^k))^(e*(r-1))*carrySum p 1 k s a := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base => simp
  | succ r hr ih =>
    intro k a ha had
    have hex : e*r = e+e*(r-1) := by
      have he : r=(r-1)+1 := by omega
      conv_lhs => rw [he, Nat.mul_add, Nat.mul_one]
      omega
    have hpow : (p:ZMod (p^k))^(e*r+1) =
        (p:ZMod (p^k))^e*(p:ZMod (p^k))^(e*(r-1)+1) := by
      rw [← pow_add]
      congr 1
      omega
    have hrec' := hrec r hr k a ha had
    have hmul : (p:ZMod (p^k))^(e*r+1) ∣
        (p:ZMod (p^k))^e*(carrySum p r k s a -
          (p:ZMod (p^k))^(e*(r-1))*carrySum p 1 k s a) := by
      rw [hpow]
      exact mul_dvd_mul (dvd_refl _) (ih k a ha had)
    have hdiv := dvd_add hrec' hmul
    have heq : carrySum p (r+1) k s a-(p:ZMod (p^k))^e*carrySum p r k s a+
        (p:ZMod (p^k))^e*(carrySum p r k s a-
          (p:ZMod (p^k))^(e*(r-1))*carrySum p 1 k s a) =
        carrySum p (r+1) k s a-(p:ZMod (p^k))^(e*r)*carrySum p 1 k s a := by
      rw [hex, pow_add]
      ring
    rw [heq] at hdiv
    simpa only [Nat.add_sub_cancel] using hdiv

/-- The same induction yields (12), (13), and (14) once their scalar
recurrences have been supplied; e is respectively 2, 1, and 2. -/
theorem scalar_scaling (p r d e : ℕ) (s : Fin d → ℕ) (hr : 1 ≤ r) (hd : 2 ≤ d)
    (hrec : ScalarCarryRecurrence p d e s) :
    sumMod p r (e*(r-1)+1) s =
      (p : ZMod (p^(e*(r-1)+1)))^(e*(r-1))*sumMod p 1 (e*(r-1)+1) s := by
  have ht := scalar_scaling_dvd p d e s hrec r hr (e*(r-1)+1) 1 (by omega) (by omega)
  rw [ZMod.natCast_pow_eq_zero_of_le p (le_refl _), zero_dvd_iff, sub_eq_zero] at ht
  simpa only [sumMod_eq_first] using ht

#print axioms scalar_scaling
end FiniteMT
```

### `ProjectionAlgebra.lean`

```lean
import ProjectedCount
import CarryReflection
open scoped BigOperators
noncomputable section
namespace FiniteMT

theorem parityProjection_add {R : Type*} [CommRing R] {n : ℕ}
    (half eta : R) (v w : Fin n → R) :
    parityProjection half eta (v+w) =
      parityProjection half eta v+parityProjection half eta w := by
  funext b
  simp only [parityProjection, Pi.add_apply]
  ring

theorem parityProjection_smul {R : Type*} [CommRing R] {n : ℕ}
    (half eta c : R) (v : Fin n → R) :
    parityProjection half eta (fun b => c*v b) =
      fun b => c*parityProjection half eta v b := by
  funext b
  simp only [parityProjection]
  ring

theorem parityProjection_complement {R : Type*} [CommRing R] {n : ℕ}
    (half eta : R) (hhalf : half*2=1) (v : Fin n → R) :
    parityProjection half eta v+parityProjection half (-eta) v = v := by
  funext b
  simp only [parityProjection, Pi.add_apply]
  calc
    _ = half*2*v b := by ring
    _ = _ := by rw [hhalf, one_mul]

theorem parityProjection_idempotent {R : Type*} [CommRing R] {n : ℕ}
    (half eta : R) (hhalf : half*2=1) (heta : eta*eta=1) (v : Fin n → R) :
    parityProjection half eta (parityProjection half eta v) = parityProjection half eta v := by
  funext b
  simp only [parityProjection, Fin.rev_rev]
  calc
    _ = half*(half*2)*(v b+eta*v b.rev) := by
      linear_combination half^2*v b*heta
    _ = _ := by rw [hhalf, mul_one]

theorem parityProjection_opposite {R : Type*} [CommRing R] {n : ℕ}
    (half eta : R) (heta : eta*eta=1) (v : Fin n → R) :
    parityProjection half eta (parityProjection half (-eta) v) = 0 := by
  funext b
  simp only [parityProjection, Fin.rev_rev, Pi.zero_apply]
  linear_combination -half^2*v b*heta

theorem carryAction_projection (p d k a : ℕ) (hp : 0 < p) (ha : a ≤ d)
    (half eta : ZMod (p^k)) (v : Fin (d-1) → ZMod (p^k)) :
    carryAction p d k (parityProjection half eta v) a =
      half*(carryAction p d k v a+eta*carryAction p d k v (d-a)) := by
  unfold carryAction parityProjection
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have he : (∑ b : Fin (d-1), (carryCount p d a (b.val+1):ZMod (p^k))*
      (half*(eta*v b.rev))) =
      ∑ b : Fin (d-1), half*(eta*((carryCount p d (d-a) (b.val+1):ZMod (p^k))*v b)) := by
    rw [← Equiv.sum_comp Fin.revPerm]
    apply Finset.sum_congr rfl
    intro b _
    simp only [Fin.revPerm_apply, Fin.rev_rev]
    have hb : b.val+1 ≤ d := by have := b.isLt; omega
    have hrev : b.rev.val+1=d-(b.val+1) := by rw [Fin.val_rev]; omega
    have hm := carryCount_reflection p d a (d-(b.val+1)) hp ha (Nat.sub_le _ _)
    rw [Nat.sub_sub_self hb] at hm
    rw [hrev, ← hm]
    ring
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem firstMoment_cast_identity (p d k a b : ℕ) (i : Fin d) (_hp : p.Prime)
    (hdp : d+1 < p) (ha : 1 ≤ a) (hbd : b < d) :
    (d : ZMod (p^k))*(firstMoment p d a b i:ZMod (p^k)) =
      ((a:ZMod (p^k))*(p:ZMod (p^k))-(b:ZMod (p^k)))*
        (carryCount p d a b:ZMod (p^k)) := by
  have hab : b ≤ a*p := by
    have : p ≤ a*p := by simpa using Nat.mul_le_mul_right p ha
    omega
  have ht := congrArg (fun t : ℕ => (t:ZMod (p^k))) (firstMoment_identity p d a b i)
  simpa only [Nat.cast_mul, Nat.cast_sub hab] using ht

#print axioms carryAction_projection
#print axioms parityProjection_idempotent
end FiniteMT
```

### `Remaining.lean`

```lean
import ProjectionAlgebra
import ShiftedParity
import ScalarScaling
namespace FiniteMT

/-- Precise next unproved helper: written proof equation (11). -/
def ProjectedCarryLift : Prop :=
  ∀ (p r d : ℕ) (s : Fin d → ℕ),
    p.Prime → 1 ≤ r → 0 < d → d+1 < p → Odd (d+weight s) →
    ∀ a, 1 ≤ a → a < d →
      carrySum p (r+1) (2*r+1) s a =
        carryAction p d (2*r+1)
          (parityProjection (2:ZMod (p^(2*r+1)))⁻¹ ((-1)^weight s)
            (fun b => carrySum p r (2*r+1) s (b.val+1))) a

def StrongCarryDivisibility : Prop :=
  ∀ (p r k d : ℕ) (s : Fin d → ℕ),
    p.Prime → 1 ≤ r → d+1 < p → Odd (d+weight s) →
    ∀ a, 1 ≤ a → a < d →
      (p:ZMod (p^k))^(2*r-2) ∣ carrySum p r k s a

def InitialCarryCancellation : Prop :=
  ∀ (p d : ℕ) (s : Fin d → ℕ), p.Prime → 0 < d →
    (∀ i, 0 < s i) → weight s+1 < p →
      (∑ b : Fin (d-1), carrySum p 1 1 s (b.val+1)) = 0

/-- Unproved concrete scalar recurrences; their common induction is already proved. -/
def ExceptionalScalarRecurrences : Prop :=
  (∀ (p : ℕ) (s : Fin 4 → ℕ), p.Prime → (∀ i, 0 < s i) →
    weight s+1 < p → Odd (weight s) → ScalarCarryRecurrence p 4 2 s) ∧
  (∀ (p : ℕ) (s : Fin 4 → ℕ), p.Prime → (∀ i, 0 < s i) →
    weight s+1 < p → Even (weight s) → ScalarCarryRecurrence p 4 1 s) ∧
  (∀ (p : ℕ) (s : Fin 5 → ℕ), p.Prime → (∀ i, 0 < s i) →
    weight s+1 < p → Even (weight s) → ScalarCarryRecurrence p 5 2 s)

/-- All three exceptional conclusions reuse scalar_scaling. -/
theorem source_of_recurrences (hrec : ExceptionalScalarRecurrences)
    (h15 : Divisibility15) : SourceConjecture := by
  apply source_of_four _ _ _ h15
  · intro p r s hp hr hs hw ho
    have ht := scalar_scaling p r 4 2 s hr (by decide) (hrec.1 p s hp hs hw ho)
    have he1 : 2*(r-1)+1=2*r-1 := by omega
    have he2 : 2*(r-1)=2*r-2 := by omega
    rw [he1, he2] at ht
    exact ht
  · intro p r s hp hr hs hw he
    have ht := scalar_scaling p r 4 1 s hr (by decide) (hrec.2.1 p s hp hs hw he)
    rw [one_mul, Nat.sub_add_cancel hr] at ht
    exact ht
  · intro p r s hp hr hs hw he
    have ht := scalar_scaling p r 5 2 s hr (by decide) (hrec.2.2 p s hp hs hw he)
    have he1 : 2*(r-1)+1=2*r-1 := by omega
    have he2 : 2*(r-1)=2*r-2 := by omega
    rw [he1, he2] at ht
    exact ht

#print axioms source_of_recurrences
end FiniteMT
```

### `ProjectedMoment.lean`

```lean
import ProjectionAlgebra
open scoped BigOperators
noncomputable section
namespace FiniteMT

theorem carryCount_pair_dvd (p d k a b : ℕ) (hp : p.Prime) (hdp : d+1 < p)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hbd : b < d) :
    (p:ZMod (p^k))^2 ∣
      (carryCount p d a b:ZMod (p^k))+
        (-1:ZMod (p^k))^(d+1)*(carryCount p d a (d-b):ZMod (p^k)) := by
  have hz (k : ℕ) (hk : k ≤ 2) :
      (carryCount p d a b:ZMod (p^k))+
        (-1:ZMod (p^k))^(d+1)*(carryCount p d a (d-b):ZMod (p^k))=0 := by
    rw [carryCount_column_parity_at p d k a b hp hdp ha hb hbd hk, pow_succ]
    have he := sign_square (R:=ZMod (p^k)) d
    calc
      _ = (1-((-1:ZMod (p^k))^d*(-1:ZMod (p^k))^d))*
          (carryCount p d a b:ZMod (p^k)) := by ring
      _ = 0 := by rw [he, sub_self, zero_mul]
  by_cases hk : 2 ≤ k
  · apply (reduction_zero_iff p 2 k hp hk _).mp
    simpa only [map_add, map_mul, map_pow, map_neg, map_one, map_natCast] using hz 2 (le_refl 2)
  · rw [hz k (by omega)]
    exact dvd_zero _

/-- Four entries of L occurring in P_eta L P_(-eta), before the factor 1/4.
This is the second-p gain needed for the projected derivative correction. -/
theorem firstMoment_cross_dvd (p d k a b : ℕ) (i : Fin d) (hp : p.Prime)
    (hdp : d+1 < p) (ha : 1 ≤ a) (had : a < d) (hb : 1 ≤ b) (hbd : b < d) :
    (p:ZMod (p^k))^2 ∣
      (firstMoment p d a b i:ZMod (p^k)) -
        (-1:ZMod (p^k))^(d+1)*(firstMoment p d a (d-b) i:ZMod (p^k)) +
        (-1:ZMod (p^k))^(d+1)*(firstMoment p d (d-a) b i:ZMod (p^k)) -
        (firstMoment p d (d-a) (d-b) i:ZMod (p^k)) := by
  by_cases hk : k=0
  · subst k
    let : Subsingleton (ZMod (p^0)) := ZMod.subsingleton_iff.mpr (pow_zero p)
    exact ⟨0, Subsingleton.elim _ _⟩
  let A := ZMod (p^k)
  let eta : A := (-1)^(d+1)
  let M : A := (carryCount p d a b:A)
  let N : A := (carryCount p d a (d-b):A)
  let C : A := (firstMoment p d a b i:A)-eta*(firstMoment p d a (d-b) i:A)+
    eta*(firstMoment p d (d-a) b i:A)-(firstMoment p d (d-a) (d-b) i:A)
  have h1 := firstMoment_cast_identity p d k a b i hp hdp ha hbd
  have h2 := firstMoment_cast_identity p d k a (d-b) i hp hdp ha (by omega)
  have h3 := firstMoment_cast_identity p d k (d-a) b i hp hdp (by omega) hbd
  have h4 := firstMoment_cast_identity p d k (d-a) (d-b) i hp hdp (by omega) (by omega)
  have hm := carryCount_reflection p d a b hp.pos (by omega) (by omega)
  have hn := carryCount_reflection p d a (d-b) hp.pos (by omega) (Nat.sub_le _ _)
  rw [Nat.sub_sub_self (Nat.le_of_lt hbd)] at hn
  rw [hm] at h4
  rw [hn] at h3
  have ha' : ((d-a:ℕ):A) = (d:A)-(a:A) := Nat.cast_sub (by omega)
  have hb' : ((d-b:ℕ):A) = (d:A)-(b:A) := Nat.cast_sub (by omega)
  have he : (d:A)*C =
      (2*(a:A)-(d:A))*(p:A)*(M-eta*N)+((d:A)-2*(b:A))*(M+eta*N) := by
    dsimp [C, M, N]
    simp only [ha', hb'] at h2 h3 h4
    linear_combination h1 - eta*h2 + eta*h3 - h4
  have hM : (p:A) ∣ M := by
    obtain ⟨q, hq⟩ := carryCount_dvd p d a b hp hdp ha hb hbd
    exact ⟨(q:A), by dsimp [M]; rw [hq, Nat.cast_mul]⟩
  have hN : (p:A) ∣ N := by
    obtain ⟨q, hq⟩ := carryCount_dvd p d a (d-b) hp hdp ha (by omega) (by omega)
    exact ⟨(q:A), by dsimp [N]; rw [hq, Nat.cast_mul]⟩
  have hpair : (p:A)^2 ∣ M+eta*N :=
    carryCount_pair_dvd p d k a b hp hdp ha hb hbd
  have hminus : (p:A) ∣ M-eta*N := dvd_sub hM (dvd_mul_of_dvd_right hN _)
  have hterm : (p:A)^2 ∣ (2*(a:A)-(d:A))*(p:A)*(M-eta*N) := by
    obtain ⟨q, hq⟩ := hminus
    refine ⟨(2*(a:A)-(d:A))*q, ?_⟩
    rw [hq]
    ring
  have hdiv : (p:A)^2 ∣ (d:A)*C := by
    rw [he]
    exact dvd_add hterm (dvd_mul_of_dvd_right hpair _)
  have hdunit := Taylor.coordinate_isUnit p k d hp (by omega)
    (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  have heC : C = (d:A)⁻¹*((d:A)*C) := by
    rw [← mul_assoc, ZMod.inv_mul_of_unit _ hdunit, one_mul]
  change (p:A)^2 ∣ C
  rw [heC]
  exact dvd_mul_of_dvd_right hdiv _

#print axioms firstMoment_cross_dvd
end FiniteMT
```

### `Stage2Inventory.lean`

```lean
import Inventory
import Remaining
import ProjectedMoment

#check FiniteMT.sumMod_depth_one
#print axioms FiniteMT.sumMod_depth_one
#check FiniteMT.sanity_weight13
#print axioms FiniteMT.sanity_weight13
#check FiniteMT.sanity_nonempty
#print axioms FiniteMT.sanity_nonempty
#check FiniteMT.sanity_scaling
#print axioms FiniteMT.sanity_scaling
#check FiniteMT.fourEquiv_symm_apply
#print axioms FiniteMT.fourEquiv_symm_apply
#check FiniteMT.sum_four
#print axioms FiniteMT.sum_four
#check FiniteMT.Taylor.jet_mul
#print axioms FiniteMT.Taylor.jet_mul
#check FiniteMT.Taylor.perturb_val
#print axioms FiniteMT.Taylor.perturb_val
#check FiniteMT.Taylor.inverse_perturb
#print axioms FiniteMT.Taylor.inverse_perturb
#check FiniteMT.Taylor.inverse_pow_perturb
#print axioms FiniteMT.Taylor.inverse_pow_perturb
#check FiniteMT.Taylor.product_jets
#print axioms FiniteMT.Taylor.product_jets
#check FiniteMT.Taylor.product_inverse_perturb
#print axioms FiniteMT.Taylor.product_inverse_perturb
#check FiniteMT.Taylor.scaled_cross_zero
#print axioms FiniteMT.Taylor.scaled_cross_zero
#check FiniteMT.Taylor.scaled_quadratic_zero
#print axioms FiniteMT.Taylor.scaled_quadratic_zero
#check FiniteMT.Taylor.sum_product_jets
#print axioms FiniteMT.Taylor.sum_product_jets
#check FiniteMT.Taylor.family_evaluate
#print axioms FiniteMT.Taylor.family_evaluate
#check FiniteMT.Taylor.sum_product_inverse_perturb
#print axioms FiniteMT.Taylor.sum_product_inverse_perturb
#check FiniteMT.Taylor.power_cube_zero
#print axioms FiniteMT.Taylor.power_cube_zero
#check FiniteMT.Taylor.quadratic_moment_zero
#print axioms FiniteMT.Taylor.quadratic_moment_zero
#check FiniteMT.Taylor.inverse_pow_lift
#print axioms FiniteMT.Taylor.inverse_pow_lift
#check FiniteMT.Taylor.coordinate_isUnit
#print axioms FiniteMT.Taylor.coordinate_isUnit
#check FiniteMT.Taylor.finite_product_inverse_lift
#print axioms FiniteMT.Taylor.finite_product_inverse_lift
#check FiniteMT.Taylor.familyCoeff_first
#print axioms FiniteMT.Taylor.familyCoeff_first
#check FiniteMT.Taylor.familyCoeff_second
#print axioms FiniteMT.Taylor.familyCoeff_second
#check FiniteMT.Taylor.scaled_const_moment_zero
#print axioms FiniteMT.Taylor.scaled_const_moment_zero
#check FiniteMT.Taylor.scaled_mixed_moment_zero
#print axioms FiniteMT.Taylor.scaled_mixed_moment_zero
#check FiniteMT.Taylor.sum_inverse_of_digit_moments
#print axioms FiniteMT.Taylor.sum_inverse_of_digit_moments
#check FiniteMT.Taylor.modular_lifted_sum
#print axioms FiniteMT.Taylor.modular_lifted_sum
#check FiniteMT.sumMod_eq_first
#print axioms FiniteMT.sumMod_eq_first
#check FiniteMT.firstMoment_total
#print axioms FiniteMT.firstMoment_total
#check FiniteMT.digitCondition_perm
#print axioms FiniteMT.digitCondition_perm
#check FiniteMT.firstMoment_symm
#print axioms FiniteMT.firstMoment_symm
#check FiniteMT.firstMoment_identity
#print axioms FiniteMT.firstMoment_identity
#check FiniteMT.firstMoment_dvd_of_count
#print axioms FiniteMT.firstMoment_dvd_of_count
#check FiniteMT.weak_divisibility_of_carry
#print axioms FiniteMT.weak_divisibility_of_carry
#check FiniteMT.assertion16_of_carry
#print axioms FiniteMT.assertion16_of_carry
#check FiniteMT.depth_le_weight
#print axioms FiniteMT.depth_le_weight
#check FiniteMT.source_of_obligations
#print axioms FiniteMT.source_of_obligations

#check FiniteMT.countTheorem
#print axioms FiniteMT.countTheorem
#check FiniteMT.weakLiftTheorem
#print axioms FiniteMT.weakLiftTheorem
#check FiniteMT.assertion16
#print axioms FiniteMT.assertion16
#check FiniteMT.source_of_four
#print axioms FiniteMT.source_of_four
#check FiniteMT.firstMoment_dvd
#print axioms FiniteMT.firstMoment_dvd
#check FiniteMT.digitFiber_sum
#print axioms FiniteMT.digitFiber_sum
#check FiniteMT.digitFiber_card
#print axioms FiniteMT.digitFiber_card
#check FiniteMT.digitFiber_first
#print axioms FiniteMT.digitFiber_first
#check FiniteMT.digitFiber_second
#print axioms FiniteMT.digitFiber_second
#check FiniteMT.linear_eq_sum
#print axioms FiniteMT.linear_eq_sum
#check FiniteMT.concrete_lifted_fiber
#print axioms FiniteMT.concrete_lifted_fiber
#check FiniteMT.reflectDigits_total
#print axioms FiniteMT.reflectDigits_total
#check FiniteMT.digitCondition_reflect
#print axioms FiniteMT.digitCondition_reflect
#check FiniteMT.carryCount_reflection
#print axioms FiniteMT.carryCount_reflection
#check FiniteMT.sum_lift_reindex
#print axioms FiniteMT.sum_lift_reindex
#check FiniteMT.carrySum_reindex
#print axioms FiniteMT.carrySum_reindex
#check FiniteMT.digitPoly_derivative
#print axioms FiniteMT.digitPoly_derivative
#check FiniteMT.digitPoly_derivative_two
#print axioms FiniteMT.digitPoly_derivative_two
#check FiniteMT.fiber_weight_coeff
#print axioms FiniteMT.fiber_weight_coeff
#check FiniteMT.mixed_secondMoment_dvd
#print axioms FiniteMT.mixed_secondMoment_dvd
#check FiniteMT.square_secondMoment_dvd
#print axioms FiniteMT.square_secondMoment_dvd
#check FiniteMT.secondMoment_dvd
#print axioms FiniteMT.secondMoment_dvd
#check FiniteMT.digitPolynomial_power
#print axioms FiniteMT.digitPolynomial_power
#check FiniteMT.count_coefficient
#print axioms FiniteMT.count_coefficient
#check FiniteMT.digitPolynomial_geom
#print axioms FiniteMT.digitPolynomial_geom
#check FiniteMT.digitPolynomial_derivative_relation
#print axioms FiniteMT.digitPolynomial_derivative_relation
#check FiniteMT.countPolynomial_differential
#print axioms FiniteMT.countPolynomial_differential
#check FiniteMT.countPolynomial_coeff_recurrence
#print axioms FiniteMT.countPolynomial_coeff_recurrence
#check FiniteMT.digitPoly_eq
#print axioms FiniteMT.digitPoly_eq
#check FiniteMT.digitPoly_power
#print axioms FiniteMT.digitPoly_power
#check FiniteMT.count_as_coeff
#print axioms FiniteMT.count_as_coeff
#check FiniteMT.expand_gap
#print axioms FiniteMT.expand_gap
#check FiniteMT.carryCount_dvd
#print axioms FiniteMT.carryCount_dvd
#check FiniteMT.p_cast_multiple_zero
#print axioms FiniteMT.p_cast_multiple_zero
#check FiniteMT.carryCount_row_recurrence
#print axioms FiniteMT.carryCount_row_recurrence
#check FiniteMT.joinDigits_sum
#print axioms FiniteMT.joinDigits_sum
#check FiniteMT.joinDigits_good
#print axioms FiniteMT.joinDigits_good
#check FiniteMT.low_carry_exists
#print axioms FiniteMT.low_carry_exists
#check FiniteMT.lift_filter
#print axioms FiniteMT.lift_filter
#check FiniteMT.shifted_product
#print axioms FiniteMT.shifted_product
#check FiniteMT.product_derivative_sum
#print axioms FiniteMT.product_derivative_sum
#check FiniteMT.carrySum_double
#print axioms FiniteMT.carrySum_double
#check FiniteMT.unit_inverse_sub
#print axioms FiniteMT.unit_inverse_sub
#check FiniteMT.product_sub_dvd
#print axioms FiniteMT.product_sub_dvd
#check FiniteMT.inverse_product_lift_dvd
#print axioms FiniteMT.inverse_product_lift_dvd
#check FiniteMT.reflectLow_val
#print axioms FiniteMT.reflectLow_val
#check FiniteMT.reflectLow_good
#print axioms FiniteMT.reflectLow_good
#check FiniteMT.reflectLow_total
#print axioms FiniteMT.reflectLow_total
#check FiniteMT.lowCondition_reflect
#print axioms FiniteMT.lowCondition_reflect
#check FiniteMT.carrySum_reflection_reindex
#print axioms FiniteMT.carrySum_reflection_reindex
#check FiniteMT.moment_gap
#print axioms FiniteMT.moment_gap
#check FiniteMT.weighted_product
#print axioms FiniteMT.weighted_product
#check FiniteMT.prod_one_factor
#print axioms FiniteMT.prod_one_factor
#check FiniteMT.prod_two_factor
#print axioms FiniteMT.prod_two_factor
#check FiniteMT.one_moment_poly
#print axioms FiniteMT.one_moment_poly
#check FiniteMT.mixed_moment_poly
#print axioms FiniteMT.mixed_moment_poly
#check FiniteMT.weightedDigitPoly_one
#print axioms FiniteMT.weightedDigitPoly_one
#check FiniteMT.weightedDigitPoly_two
#print axioms FiniteMT.weightedDigitPoly_two
#check FiniteMT.sign_square
#print axioms FiniteMT.sign_square
#check FiniteMT.carrySum_reflection_at
#print axioms FiniteMT.carrySum_reflection_at
#check FiniteMT.carrySum_parity_at
#print axioms FiniteMT.carrySum_parity_at
#check FiniteMT.carrySum_parity_difference
#print axioms FiniteMT.carrySum_parity_difference
#check FiniteMT.wrongParity_dvd
#print axioms FiniteMT.wrongParity_dvd
#check FiniteMT.wrongParity_project_dvd
#print axioms FiniteMT.wrongParity_project_dvd
#check FiniteMT.sum_reflection_cancel
#print axioms FiniteMT.sum_reflection_cancel
#check FiniteMT.carryCount_column_parity_at
#print axioms FiniteMT.carryCount_column_parity_at
#check FiniteMT.projected_count_zero
#print axioms FiniteMT.projected_count_zero
#check FiniteMT.projected_count_dvd
#print axioms FiniteMT.projected_count_dvd
#check FiniteMT.carryCount_pair_dvd
#print axioms FiniteMT.carryCount_pair_dvd
#check FiniteMT.firstMoment_cross_dvd
#print axioms FiniteMT.firstMoment_cross_dvd
#check FiniteMT.parityProjection_add
#print axioms FiniteMT.parityProjection_add
#check FiniteMT.parityProjection_smul
#print axioms FiniteMT.parityProjection_smul
#check FiniteMT.parityProjection_complement
#print axioms FiniteMT.parityProjection_complement
#check FiniteMT.parityProjection_idempotent
#print axioms FiniteMT.parityProjection_idempotent
#check FiniteMT.parityProjection_opposite
#print axioms FiniteMT.parityProjection_opposite
#check FiniteMT.carryAction_projection
#print axioms FiniteMT.carryAction_projection
#check FiniteMT.firstMoment_cast_identity
#print axioms FiniteMT.firstMoment_cast_identity
#check FiniteMT.map_zmod_unit_inverse
#print axioms FiniteMT.map_zmod_unit_inverse
#check FiniteMT.reduce_carrySum
#print axioms FiniteMT.reduce_carrySum
#check FiniteMT.reduce_sumMod
#print axioms FiniteMT.reduce_sumMod
#check FiniteMT.reduce_derivativeCarrySum
#print axioms FiniteMT.reduce_derivativeCarrySum
#check FiniteMT.carrySum_double_at
#print axioms FiniteMT.carrySum_double_at
#check FiniteMT.derivativeCarrySum_dvd
#print axioms FiniteMT.derivativeCarrySum_dvd
#check FiniteMT.carrySum_weak_plus
#print axioms FiniteMT.carrySum_weak_plus
#check FiniteMT.reduction_zero_iff
#print axioms FiniteMT.reduction_zero_iff
#check FiniteMT.reflection_product
#print axioms FiniteMT.reflection_product
#check FiniteMT.carrySum_reflection
#print axioms FiniteMT.carrySum_reflection
#check FiniteMT.source_of_recurrences
#print axioms FiniteMT.source_of_recurrences
#check FiniteMT.row_normalized
#print axioms FiniteMT.row_normalized
#check FiniteMT.row_reversal
#print axioms FiniteMT.row_reversal
#check FiniteMT.choose_isUnit_mod_prime_square
#print axioms FiniteMT.choose_isUnit_mod_prime_square
#check FiniteMT.carryCount_column_parity
#print axioms FiniteMT.carryCount_column_parity
#check FiniteMT.scalar_scaling_dvd
#print axioms FiniteMT.scalar_scaling_dvd
#check FiniteMT.scalar_scaling
#print axioms FiniteMT.scalar_scaling
#check FiniteMT.weight_shift
#print axioms FiniteMT.weight_shift
#check FiniteMT.shiftedParity_dvd
#print axioms FiniteMT.shiftedParity_dvd
#check FiniteMT.shiftedParity_project_dvd
#print axioms FiniteMT.shiftedParity_project_dvd
#check FiniteMT.digit_constant_sum
#print axioms FiniteMT.digit_constant_sum
#check FiniteMT.base_lift_sum
#print axioms FiniteMT.base_lift_sum
#check FiniteMT.weakCarryRecurrence
#print axioms FiniteMT.weakCarryRecurrence

#print FiniteMT.ProjectedCarryLift

#print FiniteMT.StrongCarryDivisibility

#print FiniteMT.InitialCarryCancellation

#print FiniteMT.ExceptionalScalarRecurrences

#print FiniteMT.ScalarCarryRecurrence
```

### `MatrixProjection.lean`

```lean
import ProjectionAlgebra
open scoped BigOperators
namespace FiniteMT
noncomputable section

def matrixAction {R : Type*} [CommRing R] {n : ℕ}
    (M : Fin n → Fin n → R) (v : Fin n → R) : Fin n → R :=
  fun a => ∑ b, M a b*v b

theorem matrixAction_add {R : Type*} [CommRing R] {n : ℕ}
    (M : Fin n → Fin n → R) (v w : Fin n → R) :
    matrixAction M (v+w) = matrixAction M v+matrixAction M w := by
  funext a
  simp [matrixAction, mul_add, Finset.sum_add_distrib]

theorem projected_matrix_action {R : Type*} [CommRing R] {n : ℕ}
    (M : Fin n → Fin n → R) (half eta : R) (v : Fin n → R) (a : Fin n) :
    parityProjection half eta (matrixAction M v) a =
      ∑ b, half*(M a b+eta*M a.rev b)*v b := by
  simp only [parityProjection, matrixAction, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Exact aggregation of the four coefficients of P_eta M P_(-eta). -/
theorem projected_matrix_cross {R : Type*} [CommRing R] {n : ℕ}
    (M : Fin n → Fin n → R) (half eta : R) (heta : eta*eta=1)
    (v : Fin n → R) (a : Fin n) :
    parityProjection half eta
      (matrixAction M (parityProjection half (-eta) v)) a =
      half^2*∑ b, (M a b-eta*M a b.rev+eta*M a.rev b-M a.rev b.rev)*v b := by
  rw [projected_matrix_action]
  simp only [parityProjection, mul_add, Finset.sum_add_distrib]
  have he : (∑ b, (half*M a b+half*(eta*M a.rev b))*(half*(-eta*v b.rev))) =
      ∑ b, (half*M a b.rev+half*(eta*M a.rev b.rev))*(half*(-eta*v b)) := by
    rw [← Equiv.sum_comp Fin.revPerm]
    simp only [Fin.revPerm_apply, Fin.rev_rev]
  rw [he, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  linear_combination -half^2*M a.rev b.rev*v b*heta

/-- Entrywise divisibility survives arbitrary finite aggregation. -/
theorem matrixAction_dvd {R : Type*} [CommRing R] {n : ℕ}
    (M : Fin n → Fin n → R) (v : Fin n → R) (q t : R)
    (hM : ∀ a b, q ∣ M a b) (hv : ∀ b, t ∣ v b) (a : Fin n) :
    q*t ∣ matrixAction M v a := by
  apply Finset.dvd_sum
  intro b _
  exact mul_dvd_mul (hM a b) (hv b)

#print axioms projected_matrix_cross
#print axioms matrixAction_dvd
end
end FiniteMT
```

### `MatrixDivisibility.lean`

```lean
import MatrixProjection
open scoped BigOperators
namespace FiniteMT
noncomputable section

theorem projected_matrix_cross_dvd {R : Type*} [CommRing R] {n : ℕ}
    (M : Fin n → Fin n → R) (half eta q t : R) (heta : eta*eta=1)
    (v : Fin n → R)
    (hM : ∀ a b, q ∣ M a b-eta*M a b.rev+eta*M a.rev b-M a.rev b.rev)
    (hv : ∀ b, t ∣ v b) (a : Fin n) :
    q*t ∣ parityProjection half eta
      (matrixAction M (parityProjection half (-eta) v)) a := by
  rw [projected_matrix_cross M half eta heta v a]
  apply dvd_mul_of_dvd_right
  apply Finset.dvd_sum
  intro b _
  exact mul_dvd_mul (hM a b) (hv b)

theorem projected_matrix_dvd {R : Type*} [CommRing R] {n : ℕ}
    (M : Fin n → Fin n → R) (half eta q t : R) (v : Fin n → R)
    (hM : ∀ a b, q ∣ M a b) (hv : ∀ b, t ∣ v b) (a : Fin n) :
    q*t ∣ parityProjection half eta (matrixAction M v) a := by
  rw [projected_matrix_action]
  apply Finset.dvd_sum
  intro b _
  exact mul_dvd_mul
    (dvd_mul_of_dvd_right (dvd_add (hM a b) (dvd_mul_of_dvd_right (hM a.rev b) _)) _)
    (hv b)

#print axioms projected_matrix_cross_dvd
#print axioms projected_matrix_dvd
end
end FiniteMT
```

### `ProjectedDerivative.lean`

```lean
import MatrixDivisibility
import ProjectedMoment
import ShiftedParity
open scoped BigOperators
noncomputable section
namespace FiniteMT

theorem half_mul_two (p k : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    (2:ZMod (p^k))⁻¹*2=1 := by
  by_cases hk : k=0
  · subst k
    let : Subsingleton (ZMod (p^0)) := ZMod.subsingleton_iff.mpr (pow_zero p)
    exact Subsingleton.elim _ _
  · exact ZMod.inv_mul_of_unit _ (Taylor.coordinate_isUnit p k 2 hp (by omega)
      (Nat.not_dvd_of_pos_of_lt (by decide) hp2))

theorem carry_rev_index {d : ℕ} (b : Fin (d-1)) :
    b.rev.val+1=d-(b.val+1) := by
  rw [Fin.val_rev]
  have := b.isLt
  omega

/-- Aggregated projected derivative gain, uniform in ambient precision. -/
theorem projected_derivative_dvd (p r k d : ℕ) (s : Fin d → ℕ)
    (hp : p.Prime) (hr : 1 ≤ r) (hd : 0 < d) (hdp : d+1 < p)
    (heta : (-1:ZMod (p^k))^weight s = (-1:ZMod (p^k))^(d+1))
    (a : Fin (d-1)) :
    (p:ZMod (p^k))^(r+1) ∣
      parityProjection (2:ZMod (p^k))⁻¹ ((-1)^weight s)
        (matrixAction (fun a b : Fin (d-1) =>
          (firstMoment p d (a.val+1) (b.val+1) ⟨0,hd⟩:ZMod (p^k)))
          (fun b => derivativeCarrySum p r k s (b.val+1))) a := by
  let A := ZMod (p^k)
  let half : A := (2:A)⁻¹
  let eta : A := (-1)^weight s
  let L : Fin (d-1) → Fin (d-1) → A := fun a b =>
    (firstMoment p d (a.val+1) (b.val+1) ⟨0,hd⟩:A)
  let U : Fin (d-1) → A := fun b => derivativeCarrySum p r k s (b.val+1)
  have hb (b : Fin (d-1)) : b.val+1 < d := by have := b.isLt; omega
  have hL : ∀ a b, (p:A) ∣ L a b := by
    intro a b
    obtain ⟨q,hq⟩ := firstMoment_dvd p d (a.val+1) (b.val+1) ⟨0,hd⟩ hp hdp
      (by omega) (by omega) (hb b)
    exact ⟨(q:A), by dsimp [L]; rw [hq, Nat.cast_mul]⟩
  have hU : ∀ b, (p:A)^(r-1) ∣ U b := fun b =>
    derivativeCarrySum_dvd p r k d (b.val+1) s hp hr hdp (by omega) (hb b)
  have hP : ∀ b, (p:A)^(2*r-1) ∣ parityProjection half eta U b := by
    intro b
    simp only [parityProjection, half, eta, U, carry_rev_index]
    exact shiftedParity_project_dvd p r k d (b.val+1) s hp hr hdp (by omega) (hb b)
  have hcross : ∀ a b, (p:A)^2 ∣ L a b-eta*L a b.rev+eta*L a.rev b-L a.rev b.rev := by
    intro a b
    simp only [L, eta, heta, carry_rev_index]
    exact firstMoment_cross_dvd p d k (a.val+1) (b.val+1) ⟨0,hd⟩ hp hdp
      (by omega) (hb a) (by omega) (hb b)
  have hsame := projected_matrix_dvd L half eta (p:A) ((p:A)^(2*r-1))
    (parityProjection half eta U) hL hP a
  have hother := projected_matrix_cross_dvd L half eta ((p:A)^2) ((p:A)^(r-1))
    (sign_square (R:=A) (weight s)) U hcross hU a
  have hp1 : (p:A)*(p:A)^(2*r-1)=(p:A)^(2*r) := by
    rw [← pow_succ']; congr 1; omega
  have hp2 : (p:A)^2*(p:A)^(r-1)=(p:A)^(r+1) := by
    rw [← pow_add]; congr 1; omega
  rw [hp1] at hsame
  rw [hp2] at hother
  have hs : (p:A)^(r+1) ∣
      parityProjection half eta (matrixAction L (parityProjection half eta U)) a :=
    dvd_trans (pow_dvd_pow _ (by omega : r+1 ≤ 2*r)) hsame
  have he : matrixAction L U =
      matrixAction L (parityProjection half eta U)+
        matrixAction L (parityProjection half (-eta) U) := by
    rw [← matrixAction_add, parityProjection_complement half eta
      (half_mul_two p k hp (by omega)) U]
  change (p:A)^(r+1) ∣ parityProjection half eta (matrixAction L U) a
  rw [he, parityProjection_add]
  exact dvd_add hs hother

#print axioms projected_derivative_dvd
end FiniteMT
```

### `ProjectedLift.lean`

```lean
import ProjectedDerivative
import Remaining
open scoped BigOperators
noncomputable section
namespace FiniteMT

theorem odd_total_sign {R : Type*} [CommRing R] (d w : ℕ) (ho : Odd (d+w)) :
    (-1:R)^w=(-1:R)^(d+1) := by
  have he : w%2=(d+1)%2 := by
    have := Nat.odd_iff.mp ho
    omega
  calc
    _ = (-1:R)^(w%2) := neg_one_pow_eq_pow_mod_two w
    _ = (-1:R)^((d+1)%2) := by rw [he]
    _ = _ := (neg_one_pow_eq_pow_mod_two (d+1)).symm

/-- Equation (11) for the literal carry sums, with no residual lift input. -/
theorem projectedCarryLift : ProjectedCarryLift := by
  intro p r d s hp hr hd hdp ho a ha had
  let k := 2*r+1
  let A := ZMod (p^k)
  let half : A := (2:A)⁻¹
  let eta : A := (-1)^weight s
  let T : Fin (d-1) → A := fun b => carrySum p r k s (b.val+1)
  let V : Fin (d-1) → A := fun b => carrySum p (r+1) k s (b.val+1)
  let L : Fin (d-1) → Fin (d-1) → A := fun a b =>
    (firstMoment p d (a.val+1) (b.val+1) ⟨0,hd⟩:A)
  let U : Fin (d-1) → A := fun b => derivativeCarrySum p r k s (b.val+1)
  have hb (b : Fin (d-1)) : b.val+1 < d := by have := b.isLt; omega
  have hV : V=parityProjection half eta V := by
    funext b
    have hdiv := wrongParity_project_dvd p (r+1) k d (b.val+1) s hp (by omega)
      hdp (by omega) (hb b)
    have hex : 2*(r+1)-1=k := by dsimp [k]; omega
    rw [hex, ZMod.natCast_pow_eq_zero_of_le p (le_refl _), zero_dvd_iff, sub_eq_zero] at hdiv
    simpa only [V, parityProjection, half, eta, carryProject, carry_rev_index] using hdiv
  have hrec : V=(fun b => carryAction p d k T (b.val+1))-
      (fun b => (p:A)^r*matrixAction L U b) := by
    funext b
    exact carrySum_double_at p r k d (b.val+1) s hp hr hd hdp (by omega) (le_refl _)
  have hlin : parityProjection half eta V =
      (fun b => carryAction p d k (parityProjection half eta T) (b.val+1))-
      (fun b => (p:A)^r*parityProjection half eta (matrixAction L U) b) := by
    funext b
    simp only [Pi.sub_apply]
    rw [carryAction_projection p d k (b.val+1) hp.pos (by omega)]
    simp only [parityProjection]
    have h1 := congrFun hrec b
    have h2 := congrFun hrec b.rev
    simp only [Pi.sub_apply, carry_rev_index] at h1 h2
    rw [h1, h2]
    ring
  have hz (b : Fin (d-1)) : (p:A)^r*parityProjection half eta (matrixAction L U) b=0 := by
    obtain ⟨q,hq⟩ := projected_derivative_dvd p r k d s hp hr hd hdp
      (odd_total_sign d (weight s) ho) b
    change parityProjection half eta (matrixAction L U) b=(p:A)^(r+1)*q at hq
    rw [hq, ← mul_assoc, ← pow_add]
    have hex : r+(r+1)=k := by dsimp [k]; omega
    rw [hex, ZMod.natCast_pow_eq_zero_of_le p (le_refl _), zero_mul]
  have ht := congrFun (hV.trans hlin) (⟨a-1, by omega⟩ : Fin (d-1))
  simp only [Pi.sub_apply, hz, sub_zero] at ht
  have he : a-1+1=a := by omega
  simpa only [V, T, half, eta, he] using ht

#print axioms projectedCarryLift
end FiniteMT
```

### `StrongDivisibility.lean`

```lean
import ProjectedLift
open scoped BigOperators
noncomputable section
namespace FiniteMT

theorem carryAction_project_power_dvd (p d k e a : ℕ)
    (v : Fin (d-1) → ZMod (p^k)) (hp : p.Prime) (hdp : d+1 < p) (ha : 1 ≤ a)
    (hv : ∀ b, (p:ZMod (p^k))^e ∣ v b) :
    (p:ZMod (p^k))^(e+2) ∣ carryAction p d k
      (parityProjection (2:ZMod (p^k))⁻¹ ((-1)^(d+1)) v) a := by
  choose q hq using hv
  have he : v=(fun b => (p:ZMod (p^k))^e*q b) := funext hq
  rw [he, parityProjection_smul]
  have hact : carryAction p d k
      (fun b => (p:ZMod (p^k))^e*
        parityProjection (2:ZMod (p^k))⁻¹ ((-1)^(d+1)) q b) a =
      (p:ZMod (p^k))^e*carryAction p d k
        (parityProjection (2:ZMod (p^k))⁻¹ ((-1)^(d+1)) q) a := by
    unfold carryAction
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hact, pow_add]
  exact mul_dvd_mul (dvd_refl _) (projected_count_dvd p d k a q hp hdp ha)

/-- A zero reduction gives divisibility at every ambient precision. -/
theorem carrySum_dvd_of_zero (p r e k d a : ℕ) (s : Fin d → ℕ) (hp : p.Prime)
    (hz : carrySum p r e s a=0) :
    (p:ZMod (p^k))^e ∣ carrySum p r k s a := by
  by_cases hk : e ≤ k
  · apply (reduction_zero_iff p e k hp hk _).mp
    rw [reduce_carrySum p r e k s a hp hk, hz]
  · have hke : k ≤ e := by omega
    have ht := congrArg (ZMod.castHom (pow_dvd_pow p hke) (ZMod (p^k))) hz
    rw [reduce_carrySum p r k e s a hp hke, map_zero] at ht
    rw [ht]
    exact dvd_zero _

theorem strongCarryDivisibility : StrongCarryDivisibility := by
  intro p r k d s hp hr hdp ho
  have hall : ∀ r, 1 ≤ r → ∀ k a, 1 ≤ a → a < d →
      (p:ZMod (p^k))^(2*r-2) ∣ carrySum p r k s a := by
    intro r hr
    induction r, hr using Nat.le_induction with
    | base => intro k a _ _; simp
    | succ r hr ih =>
      intro k a ha had
      have hd : 0 < d := by omega
      have hl := projectedCarryLift p r d s hp hr hd hdp ho a ha had
      have hg := carryAction_project_power_dvd p d (2*r+1) (2*r-2) a
        (fun b => carrySum p r (2*r+1) s (b.val+1)) hp hdp ha
        (fun b => ih (2*r+1) (b.val+1) (by omega) (by have := b.isLt; omega))
      rw [← odd_total_sign d (weight s) ho, ← hl] at hg
      have hex : 2*r-2+2=2*r := by omega
      rw [hex] at hg
      have hz : carrySum p (r+1) (2*r) s a=0 := by
        have ht := (reduction_zero_iff p (2*r) (2*r+1) hp (by omega) _).mpr hg
        rwa [reduce_carrySum p (r+1) (2*r) (2*r+1) s a hp (by omega)] at ht
      have he : 2*(r+1)-2=2*r := by omega
      rw [he]
      exact carrySum_dvd_of_zero p (r+1) (2*r) k d a s hp hz
  exact hall r hr k

/-- The source's general odd-parity assertion (15), now unconditional. -/
theorem assertion15 : Divisibility15 := by
  intro p r d s hp hr hd hs hw ho
  by_cases hd1 : d=1
  · subst d
    exact sumMod_depth_one p r (2*r-2) s
  have hdp : d+1 < p :=
    lt_of_le_of_lt (Nat.add_le_add_right (depth_le_weight s hs) 1) hw
  have ht := strongCarryDivisibility p r (2*r-2) d s hp (by omega) hdp ho 1 (by omega) (by omega)
  rw [ZMod.natCast_pow_eq_zero_of_le p (le_refl _), zero_dvd_iff] at ht
  simpa only [sumMod_eq_first] using ht

#print axioms strongCarryDivisibility
#print axioms assertion15
end FiniteMT
```

### `FieldCancellation.lean`

```lean
import Carry
import Mathlib.FieldTheory.Finite.Basic
open scoped BigOperators
noncomputable section
namespace FiniteMT

def residueCarrySum (p d : ℕ) [NeZero p] (s : Fin d → ℕ) : ZMod p :=
  ∑ x : Fin d → ZMod p,
    if (∀ i, x i ≠ 0) ∧ (∑ i, x i)=0 then ∏ i, (x i)⁻¹^s i else 0

/-- Homogeneity on the zero-sum hyperplane replaces a multinomial expansion. -/
theorem residueCarrySum_scaling (p d : ℕ) [NeZero p] (s : Fin d → ℕ) (hp : p.Prime)
    (c : ZMod p) (hc : c ≠ 0) :
    residueCarrySum p d s = (c⁻¹)^weight s*residueCarrySum p d s := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let e : (Fin d → ZMod p) ≃ (Fin d → ZMod p) :=
    { toFun := fun x i => c*x i
      invFun := fun x i => c⁻¹*x i
      left_inv := by intro x; funext i; simp [hc]
      right_inv := by intro x; funext i; simp [hc] }
  unfold residueCarrySum
  conv_lhs => rw [← Equiv.sum_comp e]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hcond : ((∀ i, c*x i ≠ 0) ∧ (∑ i, c*x i)=0) ↔
      ((∀ i, x i ≠ 0) ∧ (∑ i, x i)=0) := by
    rw [← Finset.mul_sum]
    simp [hc]
  change (if (∀ i, c*x i ≠ 0) ∧ (∑ i, c*x i)=0 then _ else _) = _
  simp only [e, Equiv.coe_fn_mk, hcond]
  split_ifs
  · simp only [mul_inv_rev, mul_pow, Finset.prod_mul_distrib]
    rw [Finset.prod_pow_eq_pow_sum]
    unfold weight
    ring
  · exact (mul_zero _).symm

theorem residueCarrySum_zero (p d : ℕ) [NeZero p] (s : Fin d → ℕ) (hp : p.Prime)
    (hw0 : 0 < weight s) (hw : weight s < p-1) : residueCarrySum p d s=0 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨u,hu⟩ := exists_pow_ne_one_of_isCyclic (G:=(ZMod p)ˣ)
    (Nat.ne_of_gt hw0) (by simpa only [Nat.card_eq_fintype_card, ZMod.card_units] using hw)
  have hne : (u:ZMod p)^weight s ≠ 1 := by
    intro he
    apply hu
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using he
  have ht := residueCarrySum_scaling p d s hp (↑u⁻¹) (Units.ne_zero _)
  have hinv : (↑u⁻¹:ZMod p)⁻¹=(u:ZMod p) := by rw [Units.val_inv_eq_inv_val, inv_inv]
  rw [hinv] at ht
  have hm : ((u:ZMod p)^weight s-1)*residueCarrySum p d s=0 := by
    rw [sub_mul, one_mul, ← ht, sub_self]
  exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hne)

#print axioms residueCarrySum_zero
end FiniteMT
```

### `InitialCarry.lean`

```lean
import FieldCancellation
import Remaining
open scoped BigOperators
noncomputable section
set_option linter.unusedSimpArgs false
namespace FiniteMT

theorem carry_indicator_sum {R : Type*} [AddCommMonoid R] (p d S : ℕ) (v : R)
    (hp : 0 < p) (hS : 0 < S) (hSd : S < d*p) :
    (∑ b : Fin (d-1), if S=(b.val+1)*p then v else 0) = if p ∣ S then v else 0 := by
  classical
  by_cases hz : p ∣ S
  · have hz' := hz
    obtain ⟨q,hq⟩ := hz
    have hq0 : 0 < q := by nlinarith
    have hqd : q < d := by nlinarith
    let b : Fin (d-1) := ⟨q-1,by omega⟩
    have he (j : Fin (d-1)) : S=(j.val+1)*p ↔ j=b := by
      constructor
      · intro hj
        apply Fin.ext
        dsimp [b]
        have : j.val+1=q := by nlinarith
        omega
      · intro hj
        subst j
        dsimp [b]
        rw [Nat.sub_add_cancel hq0, hq, Nat.mul_comm]
    simp only [he, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hz']
  · rw [ite_eq_right hz]
    apply Finset.sum_eq_zero
    intro b _
    apply ite_eq_right
    intro he
    exact hz ⟨b.val+1, by rw [he, Nat.mul_comm]⟩

theorem initial_total_reindex (p d : ℕ) [NeZero p] (s : Fin d → ℕ)
    (hp : p.Prime) (hd : 0 < d) :
    (∑ b : Fin (d-1), ∑ x : Fin d → Fin p,
      if (∀ i, 0 < (x i).val ∧ ¬ p ∣ (x i).val) ∧
          (∑ i, (x i).val)=(b.val+1)*p
      then ∏ i, (((x i).val:ZMod p)⁻¹)^s i else 0)=residueCarrySum p d s := by
  classical
  rw [Finset.sum_comm]
  let e : (Fin d → Fin p) ≃ (Fin d → ZMod p) :=
    Equiv.piCongrRight (fun _ => (ZMod.finEquiv p).toEquiv)
  unfold residueCarrySum
  conv_rhs => rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro x _
  have hex (i : Fin d) : e x i = ((x i).val:ZMod p) := by
    cases p with
    | zero => exact (hp.ne_zero rfl).elim
    | succ p => exact (ZMod.natCast_zmod_val (n:=p+1) (x i)).symm
  have hn (i : Fin d) : (x i).val=0 ↔ p ∣ (x i).val := by
    constructor
    · intro hi; rw [hi]; exact dvd_zero _
    · intro hi; exact (Nat.eq_zero_of_dvd_of_lt hi (x i).isLt)
  have hg : (∀ i, 0 < (x i).val ∧ ¬ p ∣ (x i).val) ↔ (∀ i, e x i ≠ 0) := by
    simp only [hex, Ne, ZMod.natCast_eq_zero_iff]
    constructor
    · exact fun h i => (h i).2
    · intro h i
      exact ⟨by have := hn i; have := h i; omega, h i⟩
  have hs : (∑ i, e x i)=0 ↔ p ∣ ∑ i, (x i).val := by
    simp only [hex, ← Nat.cast_sum, ZMod.natCast_eq_zero_iff]
  have hpval : (∏ i, (((x i).val:ZMod p)⁻¹)^s i) = ∏ i, (e x i)⁻¹^s i := by
    simp only [hex]
  by_cases hx : ∀ i, 0 < (x i).val ∧ ¬ p ∣ (x i).val
  · have hS : 0 < ∑ i, (x i).val := by
      exact Finset.sum_pos (fun i _ => (hx i).1) ⟨⟨0,hd⟩,Finset.mem_univ _⟩
    have hSd : (∑ i, (x i).val) < d*p := by
      calc
        _ < ∑ _i : Fin d, p := Finset.sum_lt_sum (fun i _ => Nat.le_of_lt (x i).isLt)
          ⟨⟨0,hd⟩,Finset.mem_univ _,(x _).isLt⟩
        _ = d*p := by simp
    have hres : ∀ i, e x i ≠ 0 := hg.mp hx
    have he (b : Fin (d-1)) :
        ((∀ i, 0 < (x i).val ∧ ¬ p ∣ (x i).val) ∧
          (∑ i, (x i).val)=(b.val+1)*p) ↔ (∑ i, (x i).val)=(b.val+1)*p :=
      and_iff_right hx
    have hr : ((∀ i, e x i ≠ 0) ∧ (∑ i, e x i)=0) ↔ p ∣ ∑ i, (x i).val := by
      rw [and_iff_right hres, hs]
    simp only [he, hr, ← hpval]
    exact carry_indicator_sum (R:=ZMod p) p d _ (∏ i, (((x i).val:ZMod p)⁻¹)^s i) hp.pos hS hSd
  · have hres : ¬ (∀ i, e x i ≠ 0) := fun h => hx (hg.mpr h)
    simp only [hx, hres, false_and, ite_false, Finset.sum_const_zero]

/-- Concrete source cancellation, using uniform scaling in the finite field. -/
theorem initialCarryCancellation : InitialCarryCancellation := by
  intro p d s hp hd hs hw
  let : NeZero p := ⟨hp.ne_zero⟩
  have hz := residueCarrySum_zero p d s hp
    (lt_of_lt_of_le hd (depth_le_weight s hs)) (by omega)
  rw [← initial_total_reindex p d s hp hd] at hz
  have haux (q : ℕ) (h : q=p) :
      (∑ b : Fin (d-1), ∑ x : Fin d → Fin q,
        if (∀ i, 0 < (x i).val ∧ ¬ p ∣ (x i).val) ∧
            (∑ i, (x i).val)=(b.val+1)*q
        then ∏ i, (((x i).val:ZMod q)⁻¹)^s i else 0)=0 := by
    subst q
    exact hz
  exact haux (p^1) (pow_one p)

#print axioms initialCarryCancellation
end FiniteMT
```

### `CarryFormula.lean`

```lean
import CountGenerating
import Mathlib.RingTheory.PowerSeries.WellKnown
open scoped BigOperators
open Polynomial
noncomputable section
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace FiniteMT

/-- Exact generating function in formal power series. -/
theorem count_series (R : Type*) [CommRing R] (p d : ℕ) :
    ((digitPolynomial R p)^d).toPowerSeries =
      ((1-PowerSeries.X^p)^d : PowerSeries R) * (PowerSeries.invOneSubPow R d).val := by
  have hg := congrArg (fun f : R[X] => f.toPowerSeries) (digitPolynomial_geom R p)
  have hge : (1-PowerSeries.X : PowerSeries R)* (digitPolynomial R p).toPowerSeries=
      1-PowerSeries.X^p := by simpa using hg
  have he : (1-PowerSeries.X : PowerSeries R)^d *
      ((digitPolynomial R p)^d).toPowerSeries=(1-PowerSeries.X^p)^d := by
    simpa only [Polynomial.coe_pow, mul_pow] using congrArg (fun f : PowerSeries R => f^d) hge
  have hi : (1-PowerSeries.X : PowerSeries R)^d * (PowerSeries.invOneSubPow R d).val=1 := by
    rw [← PowerSeries.invOneSubPow_inv_eq_one_sub_pow]
    exact (PowerSeries.invOneSubPow R d).inv_val
  calc
    _ = ((1-PowerSeries.X)^d * ((digitPolynomial R p)^d).toPowerSeries) *
        (PowerSeries.invOneSubPow R d).val := by rw [mul_right_comm, hi, one_mul]
    _ = _ := by rw [he]

#print axioms count_series
end FiniteMT
```

### `CarryFormulaCoeff.lean`

```lean
import CarryFormula
open scoped BigOperators
open Polynomial
noncomputable section
namespace FiniteMT
/-- Inclusion-exclusion with its coefficient cutoffs retained explicitly. -/
theorem count_formula_cutoff (R : Type*) [CommRing R] (p d a b : ℕ)
    (hd : 0 < d) (hb : b ≤ a*p) :
    (carryCount p d a b:R) =
      ∑ j ∈ Finset.range (d+1),
        if p*j ≤ a*p-b then
          (-1:R)^j*(d.choose j:R)*((d-1+(a*p-b-p*j)).choose (d-1):R)
        else 0 := by
  rw [count_coefficient R p d a b hb]
  rw [← Polynomial.coeff_coe, count_series]
  rw [sub_eq_add_neg, add_comm (1:PowerSeries R), add_pow]
  simp only [one_pow, mul_one, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [neg_pow, ← pow_mul]
  have he : ((-1:PowerSeries R)^j*PowerSeries.X^(p*j)*(d.choose j:PowerSeries R))*
      (PowerSeries.invOneSubPow R d).val =
      PowerSeries.C ((-1:R)^j*(d.choose j:R)) *
        (PowerSeries.X^(p*j)*(PowerSeries.invOneSubPow R d).val) := by
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
    ring
  rw [he, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  simp only [PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos R d hd,
    PowerSeries.coeff_mk]
  split_ifs <;> simp_all only [mul_zero, mul_assoc]

#print axioms count_formula_cutoff
end FiniteMT
```

### `SmallChoose.lean`

```lean
import CountGenerating
open scoped BigOperators
namespace FiniteMT

theorem choose_three_shift (n : ℕ) :
    6*((3+n).choose 3:ℤ)=((n:ℤ)+1)*((n:ℤ)+2)*((n:ℤ)+3) := by
  have ht := congrArg (fun t : ℕ => (t:ℤ)) (Nat.ascFactorial_eq_factorial_mul_choose n 3)
  norm_num [Nat.ascFactorial_succ, Nat.factorial] at ht
  rw [Nat.add_comm 3 n]
  linear_combination -ht

theorem choose_four_shift (n : ℕ) :
    24*((4+n).choose 4:ℤ)=((n:ℤ)+1)*((n:ℤ)+2)*((n:ℤ)+3)*((n:ℤ)+4) := by
  have ht := congrArg (fun t : ℕ => (t:ℤ)) (Nat.ascFactorial_eq_factorial_mul_choose n 4)
  norm_num [Nat.ascFactorial_succ, Nat.factorial] at ht
  rw [Nat.add_comm 4 n]
  linear_combination -ht

#print axioms choose_three_shift
#print axioms choose_four_shift
end FiniteMT
```

### `CarryFormulaRange.lean`

```lean
import CarryFormulaCoeff
open scoped BigOperators
noncomputable section
namespace FiniteMT

theorem count_formula (R : Type*) [CommRing R] (p d a b : ℕ)
    (hp : d < p) (ha : 1 ≤ a) (had : a ≤ d) (hb : 1 ≤ b) (hbd : b < d) :
    (carryCount p d a b:R) =
      ∑ j ∈ Finset.range a,
        (-1:R)^j*(d.choose j:R)*((d-1+(a*p-b-p*j)).choose (d-1):R) := by
  have hap : p ≤ a*p := by simpa using Nat.mul_le_mul_right p ha
  rw [count_formula_cutoff R p d a b (by omega) (by omega)]
  symm
  calc
    _ = ∑ j ∈ Finset.range a, if p*j ≤ a*p-b then
        (-1:R)^j*(d.choose j:R)*((d-1+(a*p-b-p*j)).choose (d-1):R) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have hmul : p*j+b ≤ a*p := by nlinarith
      rw [ite_eq_left (by omega)]
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j _ hj
      have hj' : a ≤ j := by simpa only [Finset.mem_range, not_lt] using hj
      have hmul : a*p ≤ p*j := by nlinarith
      rw [ite_eq_right (by omega)]

#print axioms count_formula
end FiniteMT
```

### `Count4Row1.lean`

```lean
import CarryFormulaRange
import SmallChoose
namespace FiniteMT

theorem scaled_count_4_1_1 (p : ℕ) (hp : 4 < p) :
    6*(carryCount p 4 1 1:ℤ) = (2)*(p:ℤ)^1 + (3)*(p:ℤ)^2 + (1)*(p:ℤ)^3 := by
  have hc : (carryCount p 4 1 1:ℤ)=(1)*((3+(1*p-1-p*0)).choose 3:ℤ) := by
    rw [count_formula ℤ p 4 1 1 hp (by omega) (by omega) (by omega) (by omega)]
    norm_num [Finset.sum_range_succ]
  have hn0 : (1*p-1-p*0)+1+p*0=1*p := by omega
  have hcast0 : (((1*p-1-p*0):ℕ):ℤ)=(1:ℤ)*p-1-p*0 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn0
    push_cast at ht
    linarith
  have h0 := choose_three_shift (1*p-1-p*0)
  rw [hcast0] at h0
  linear_combination 6*hc + (1)*h0
#print axioms scaled_count_4_1_1

theorem scaled_count_4_1_2 (p : ℕ) (hp : 4 < p) :
    6*(carryCount p 4 1 2:ℤ) = (-1)*(p:ℤ)^1 + (1)*(p:ℤ)^3 := by
  have hc : (carryCount p 4 1 2:ℤ)=(1)*((3+(1*p-2-p*0)).choose 3:ℤ) := by
    rw [count_formula ℤ p 4 1 2 hp (by omega) (by omega) (by omega) (by omega)]
    norm_num [Finset.sum_range_succ]
  have hn0 : (1*p-2-p*0)+2+p*0=1*p := by omega
  have hcast0 : (((1*p-2-p*0):ℕ):ℤ)=(1:ℤ)*p-2-p*0 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn0
    push_cast at ht
    linarith
  have h0 := choose_three_shift (1*p-2-p*0)
  rw [hcast0] at h0
  linear_combination 6*hc + (1)*h0
#print axioms scaled_count_4_1_2

theorem scaled_count_4_1_3 (p : ℕ) (hp : 4 < p) :
    6*(carryCount p 4 1 3:ℤ) = (2)*(p:ℤ)^1 + (-3)*(p:ℤ)^2 + (1)*(p:ℤ)^3 := by
  have hc : (carryCount p 4 1 3:ℤ)=(1)*((3+(1*p-3-p*0)).choose 3:ℤ) := by
    rw [count_formula ℤ p 4 1 3 hp (by omega) (by omega) (by omega) (by omega)]
    norm_num [Finset.sum_range_succ]
  have hn0 : (1*p-3-p*0)+3+p*0=1*p := by omega
  have hcast0 : (((1*p-3-p*0):ℕ):ℤ)=(1:ℤ)*p-3-p*0 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn0
    push_cast at ht
    linarith
  have h0 := choose_three_shift (1*p-3-p*0)
  rw [hcast0] at h0
  linear_combination 6*hc + (1)*h0
#print axioms scaled_count_4_1_3
end FiniteMT
```

### `Count4Row2.lean`

```lean
import CarryFormulaRange
import SmallChoose
namespace FiniteMT

theorem scaled_count_4_2_1 (p : ℕ) (hp : 4 < p) :
    6*(carryCount p 4 2 1:ℤ) = (-4)*(p:ℤ)^1 + (4)*(p:ℤ)^3 := by
  have hc : (carryCount p 4 2 1:ℤ)=(1)*((3+(2*p-1-p*0)).choose 3:ℤ) + (-4)*((3+(2*p-1-p*1)).choose 3:ℤ) := by
    rw [count_formula ℤ p 4 2 1 hp (by omega) (by omega) (by omega) (by omega)]
    norm_num [Finset.sum_range_succ]
  have hn0 : (2*p-1-p*0)+1+p*0=2*p := by omega
  have hcast0 : (((2*p-1-p*0):ℕ):ℤ)=(2:ℤ)*p-1-p*0 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn0
    push_cast at ht
    linarith
  have h0 := choose_three_shift (2*p-1-p*0)
  rw [hcast0] at h0
  have hn1 : (2*p-1-p*1)+1+p*1=2*p := by omega
  have hcast1 : (((2*p-1-p*1):ℕ):ℤ)=(2:ℤ)*p-1-p*1 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn1
    push_cast at ht
    linarith
  have h1 := choose_three_shift (2*p-1-p*1)
  rw [hcast1] at h1
  linear_combination 6*hc + (1)*h0 + (-4)*h1
#print axioms scaled_count_4_2_1

theorem scaled_count_4_2_2 (p : ℕ) (hp : 4 < p) :
    6*(carryCount p 4 2 2:ℤ) = (2)*(p:ℤ)^1 + (4)*(p:ℤ)^3 := by
  have hc : (carryCount p 4 2 2:ℤ)=(1)*((3+(2*p-2-p*0)).choose 3:ℤ) + (-4)*((3+(2*p-2-p*1)).choose 3:ℤ) := by
    rw [count_formula ℤ p 4 2 2 hp (by omega) (by omega) (by omega) (by omega)]
    norm_num [Finset.sum_range_succ]
  have hn0 : (2*p-2-p*0)+2+p*0=2*p := by omega
  have hcast0 : (((2*p-2-p*0):ℕ):ℤ)=(2:ℤ)*p-2-p*0 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn0
    push_cast at ht
    linarith
  have h0 := choose_three_shift (2*p-2-p*0)
  rw [hcast0] at h0
  have hn1 : (2*p-2-p*1)+2+p*1=2*p := by omega
  have hcast1 : (((2*p-2-p*1):ℕ):ℤ)=(2:ℤ)*p-2-p*1 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn1
    push_cast at ht
    linarith
  have h1 := choose_three_shift (2*p-2-p*1)
  rw [hcast1] at h1
  linear_combination 6*hc + (1)*h0 + (-4)*h1
#print axioms scaled_count_4_2_2

theorem scaled_count_4_2_3 (p : ℕ) (hp : 4 < p) :
    6*(carryCount p 4 2 3:ℤ) = (-4)*(p:ℤ)^1 + (4)*(p:ℤ)^3 := by
  have hc : (carryCount p 4 2 3:ℤ)=(1)*((3+(2*p-3-p*0)).choose 3:ℤ) + (-4)*((3+(2*p-3-p*1)).choose 3:ℤ) := by
    rw [count_formula ℤ p 4 2 3 hp (by omega) (by omega) (by omega) (by omega)]
    norm_num [Finset.sum_range_succ]
  have hn0 : (2*p-3-p*0)+3+p*0=2*p := by omega
  have hcast0 : (((2*p-3-p*0):ℕ):ℤ)=(2:ℤ)*p-3-p*0 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn0
    push_cast at ht
    linarith
  have h0 := choose_three_shift (2*p-3-p*0)
  rw [hcast0] at h0
  have hn1 : (2*p-3-p*1)+3+p*1=2*p := by omega
  have hcast1 : (((2*p-3-p*1):ℕ):ℤ)=(2:ℤ)*p-3-p*1 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn1
    push_cast at ht
    linarith
  have h1 := choose_three_shift (2*p-3-p*1)
  rw [hcast1] at h1
  linear_combination 6*hc + (1)*h0 + (-4)*h1
#print axioms scaled_count_4_2_3
end FiniteMT
```

### `Count4Row3.lean`

```lean
import CarryFormulaRange
import SmallChoose
namespace FiniteMT

theorem scaled_count_4_3_1 (p : ℕ) (hp : 4 < p) :
    6*(carryCount p 4 3 1:ℤ) = (2)*(p:ℤ)^1 + (-3)*(p:ℤ)^2 + (1)*(p:ℤ)^3 := by
  have hc : (carryCount p 4 3 1:ℤ)=(1)*((3+(3*p-1-p*0)).choose 3:ℤ) + (-4)*((3+(3*p-1-p*1)).choose 3:ℤ) + (6)*((3+(3*p-1-p*2)).choose 3:ℤ) := by
    rw [count_formula ℤ p 4 3 1 hp (by omega) (by omega) (by omega) (by omega)]
    norm_num [Finset.sum_range_succ, (show (4:ℕ).choose 0=1 from by decide), (show (4:ℕ).choose 1=4 from by decide), (show (4:ℕ).choose 2=6 from by decide), (show (4:ℕ).choose 3=4 from by decide), (show (4:ℕ).choose 4=1 from by decide)]
  have hn0 : (3*p-1-p*0)+1+p*0=3*p := by omega
  have hcast0 : (((3*p-1-p*0):ℕ):ℤ)=(3:ℤ)*p-1-p*0 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn0
    push_cast at ht
    linarith
  have h0 := choose_three_shift (3*p-1-p*0)
  rw [hcast0] at h0
  have hn1 : (3*p-1-p*1)+1+p*1=3*p := by omega
  have hcast1 : (((3*p-1-p*1):ℕ):ℤ)=(3:ℤ)*p-1-p*1 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn1
    push_cast at ht
    linarith
  have h1 := choose_three_shift (3*p-1-p*1)
  rw [hcast1] at h1
  have hn2 : (3*p-1-p*2)+1+p*2=3*p := by omega
  have hcast2 : (((3*p-1-p*2):ℕ):ℤ)=(3:ℤ)*p-1-p*2 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn2
    push_cast at ht
    linarith
  have h2 := choose_three_shift (3*p-1-p*2)
  rw [hcast2] at h2
  linear_combination 6*hc + (1)*h0 + (-4)*h1 + (6)*h2
#print axioms scaled_count_4_3_1

theorem scaled_count_4_3_2 (p : ℕ) (hp : 4 < p) :
    6*(carryCount p 4 3 2:ℤ) = (-1)*(p:ℤ)^1 + (1)*(p:ℤ)^3 := by
  have hc : (carryCount p 4 3 2:ℤ)=(1)*((3+(3*p-2-p*0)).choose 3:ℤ) + (-4)*((3+(3*p-2-p*1)).choose 3:ℤ) + (6)*((3+(3*p-2-p*2)).choose 3:ℤ) := by
    rw [count_formula ℤ p 4 3 2 hp (by omega) (by omega) (by omega) (by omega)]
    norm_num [Finset.sum_range_succ, (show (4:ℕ).choose 0=1 from by decide), (show (4:ℕ).choose 1=4 from by decide), (show (4:ℕ).choose 2=6 from by decide), (show (4:ℕ).choose 3=4 from by decide), (show (4:ℕ).choose 4=1 from by decide)]
  have hn0 : (3*p-2-p*0)+2+p*0=3*p := by omega
  have hcast0 : (((3*p-2-p*0):ℕ):ℤ)=(3:ℤ)*p-2-p*0 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn0
    push_cast at ht
    linarith
  have h0 := choose_three_shift (3*p-2-p*0)
  rw [hcast0] at h0
  have hn1 : (3*p-2-p*1)+2+p*1=3*p := by omega
  have hcast1 : (((3*p-2-p*1):ℕ):ℤ)=(3:ℤ)*p-2-p*1 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn1
    push_cast at ht
    linarith
  have h1 := choose_three_shift (3*p-2-p*1)
  rw [hcast1] at h1
  have hn2 : (3*p-2-p*2)+2+p*2=3*p := by omega
  have hcast2 : (((3*p-2-p*2):ℕ):ℤ)=(3:ℤ)*p-2-p*2 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn2
    push_cast at ht
    linarith
  have h2 := choose_three_shift (3*p-2-p*2)
  rw [hcast2] at h2
  linear_combination 6*hc + (1)*h0 + (-4)*h1 + (6)*h2
#print axioms scaled_count_4_3_2

theorem scaled_count_4_3_3 (p : ℕ) (hp : 4 < p) :
    6*(carryCount p 4 3 3:ℤ) = (2)*(p:ℤ)^1 + (3)*(p:ℤ)^2 + (1)*(p:ℤ)^3 := by
  have hc : (carryCount p 4 3 3:ℤ)=(1)*((3+(3*p-3-p*0)).choose 3:ℤ) + (-4)*((3+(3*p-3-p*1)).choose 3:ℤ) + (6)*((3+(3*p-3-p*2)).choose 3:ℤ) := by
    rw [count_formula ℤ p 4 3 3 hp (by omega) (by omega) (by omega) (by omega)]
    norm_num [Finset.sum_range_succ, (show (4:ℕ).choose 0=1 from by decide), (show (4:ℕ).choose 1=4 from by decide), (show (4:ℕ).choose 2=6 from by decide), (show (4:ℕ).choose 3=4 from by decide), (show (4:ℕ).choose 4=1 from by decide)]
  have hn0 : (3*p-3-p*0)+3+p*0=3*p := by omega
  have hcast0 : (((3*p-3-p*0):ℕ):ℤ)=(3:ℤ)*p-3-p*0 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn0
    push_cast at ht
    linarith
  have h0 := choose_three_shift (3*p-3-p*0)
  rw [hcast0] at h0
  have hn1 : (3*p-3-p*1)+3+p*1=3*p := by omega
  have hcast1 : (((3*p-3-p*1):ℕ):ℤ)=(3:ℤ)*p-3-p*1 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn1
    push_cast at ht
    linarith
  have h1 := choose_three_shift (3*p-3-p*1)
  rw [hcast1] at h1
  have hn2 : (3*p-3-p*2)+3+p*2=3*p := by omega
  have hcast2 : (((3*p-3-p*2):ℕ):ℤ)=(3:ℤ)*p-3-p*2 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn2
    push_cast at ht
    linarith
  have h2 := choose_three_shift (3*p-3-p*2)
  rw [hcast2] at h2
  linear_combination 6*hc + (1)*h0 + (-4)*h1 + (6)*h2
#print axioms scaled_count_4_3_3
end FiniteMT
```

### `Count5Row1.lean`

```lean
import CarryFormulaRange
import SmallChoose
namespace FiniteMT

theorem scaled_count_5_1_1 (p : ℕ) (hp : 5 < p) :
    24*(carryCount p 5 1 1:ℤ) = (6)*(p:ℤ)^1 + (11)*(p:ℤ)^2 + (6)*(p:ℤ)^3 + (1)*(p:ℤ)^4 := by
  have hc : (carryCount p 5 1 1:ℤ)=(1)*((4+(1*p-1-p*0)).choose 4:ℤ) := by
    rw [count_formula ℤ p 5 1 1 hp (by omega) (by omega) (by omega) (by omega)]
    norm_num [Finset.sum_range_succ, (show (5:ℕ).choose 0=1 from by decide), (show (5:ℕ).choose 1=5 from by decide), (show (5:ℕ).choose 2=10 from by decide), (show (5:ℕ).choose 3=10 from by decide), (show (5:ℕ).choose 4=5 from by decide), (show (5:ℕ).choose 5=1 from by decide)]
  have hn0 : (1*p-1-p*0)+1+p*0=1*p := by omega
  have hcast0 : (((1*p-1-p*0):ℕ):ℤ)=(1:ℤ)*p-1-p*0 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn0
    push_cast at ht
    linarith
  have h0 := choose_four_shift (1*p-1-p*0)
  rw [hcast0] at h0
  linear_combination 24*hc + (1)*h0
#print axioms scaled_count_5_1_1

theorem scaled_count_5_1_2 (p : ℕ) (hp : 5 < p) :
    24*(carryCount p 5 1 2:ℤ) = (-2)*(p:ℤ)^1 + (-1)*(p:ℤ)^2 + (2)*(p:ℤ)^3 + (1)*(p:ℤ)^4 := by
  have hc : (carryCount p 5 1 2:ℤ)=(1)*((4+(1*p-2-p*0)).choose 4:ℤ) := by
    rw [count_formula ℤ p 5 1 2 hp (by omega) (by omega) (by omega) (by omega)]
    norm_num [Finset.sum_range_succ, (show (5:ℕ).choose 0=1 from by decide), (show (5:ℕ).choose 1=5 from by decide), (show (5:ℕ).choose 2=10 from by decide), (show (5:ℕ).choose 3=10 from by decide), (show (5:ℕ).choose 4=5 from by decide), (show (5:ℕ).choose 5=1 from by decide)]
  have hn0 : (1*p-2-p*0)+2+p*0=1*p := by omega
  have hcast0 : (((1*p-2-p*0):ℕ):ℤ)=(1:ℤ)*p-2-p*0 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn0
    push_cast at ht
    linarith
  have h0 := choose_four_shift (1*p-2-p*0)
  rw [hcast0] at h0
  linear_combination 24*hc + (1)*h0
#print axioms scaled_count_5_1_2

theorem scaled_count_5_1_3 (p : ℕ) (hp : 5 < p) :
    24*(carryCount p 5 1 3:ℤ) = (2)*(p:ℤ)^1 + (-1)*(p:ℤ)^2 + (-2)*(p:ℤ)^3 + (1)*(p:ℤ)^4 := by
  have hc : (carryCount p 5 1 3:ℤ)=(1)*((4+(1*p-3-p*0)).choose 4:ℤ) := by
    rw [count_formula ℤ p 5 1 3 hp (by omega) (by omega) (by omega) (by omega)]
    norm_num [Finset.sum_range_succ, (show (5:ℕ).choose 0=1 from by decide), (show (5:ℕ).choose 1=5 from by decide), (show (5:ℕ).choose 2=10 from by decide), (show (5:ℕ).choose 3=10 from by decide), (show (5:ℕ).choose 4=5 from by decide), (show (5:ℕ).choose 5=1 from by decide)]
  have hn0 : (1*p-3-p*0)+3+p*0=1*p := by omega
  have hcast0 : (((1*p-3-p*0):ℕ):ℤ)=(1:ℤ)*p-3-p*0 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn0
    push_cast at ht
    linarith
  have h0 := choose_four_shift (1*p-3-p*0)
  rw [hcast0] at h0
  linear_combination 24*hc + (1)*h0
#print axioms scaled_count_5_1_3

theorem scaled_count_5_1_4 (p : ℕ) (hp : 5 < p) :
    24*(carryCount p 5 1 4:ℤ) = (-6)*(p:ℤ)^1 + (11)*(p:ℤ)^2 + (-6)*(p:ℤ)^3 + (1)*(p:ℤ)^4 := by
  have hc : (carryCount p 5 1 4:ℤ)=(1)*((4+(1*p-4-p*0)).choose 4:ℤ) := by
    rw [count_formula ℤ p 5 1 4 hp (by omega) (by omega) (by omega) (by omega)]
    norm_num [Finset.sum_range_succ, (show (5:ℕ).choose 0=1 from by decide), (show (5:ℕ).choose 1=5 from by decide), (show (5:ℕ).choose 2=10 from by decide), (show (5:ℕ).choose 3=10 from by decide), (show (5:ℕ).choose 4=5 from by decide), (show (5:ℕ).choose 5=1 from by decide)]
  have hn0 : (1*p-4-p*0)+4+p*0=1*p := by omega
  have hcast0 : (((1*p-4-p*0):ℕ):ℤ)=(1:ℤ)*p-4-p*0 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn0
    push_cast at ht
    linarith
  have h0 := choose_four_shift (1*p-4-p*0)
  rw [hcast0] at h0
  linear_combination 24*hc + (1)*h0
#print axioms scaled_count_5_1_4
end FiniteMT
```

### `Count5Row2.lean`

```lean
import CarryFormulaRange
import SmallChoose
namespace FiniteMT

theorem scaled_count_5_2_1 (p : ℕ) (hp : 5 < p) :
    24*(carryCount p 5 2 1:ℤ) = (-18)*(p:ℤ)^1 + (-11)*(p:ℤ)^2 + (18)*(p:ℤ)^3 + (11)*(p:ℤ)^4 := by
  have hc : (carryCount p 5 2 1:ℤ)=(1)*((4+(2*p-1-p*0)).choose 4:ℤ) + (-5)*((4+(2*p-1-p*1)).choose 4:ℤ) := by
    rw [count_formula ℤ p 5 2 1 hp (by omega) (by omega) (by omega) (by omega)]
    norm_num [Finset.sum_range_succ, (show (5:ℕ).choose 0=1 from by decide), (show (5:ℕ).choose 1=5 from by decide), (show (5:ℕ).choose 2=10 from by decide), (show (5:ℕ).choose 3=10 from by decide), (show (5:ℕ).choose 4=5 from by decide), (show (5:ℕ).choose 5=1 from by decide)]
  have hn0 : (2*p-1-p*0)+1+p*0=2*p := by omega
  have hcast0 : (((2*p-1-p*0):ℕ):ℤ)=(2:ℤ)*p-1-p*0 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn0
    push_cast at ht
    linarith
  have h0 := choose_four_shift (2*p-1-p*0)
  rw [hcast0] at h0
  have hn1 : (2*p-1-p*1)+1+p*1=2*p := by omega
  have hcast1 : (((2*p-1-p*1):ℕ):ℤ)=(2:ℤ)*p-1-p*1 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn1
    push_cast at ht
    linarith
  have h1 := choose_four_shift (2*p-1-p*1)
  rw [hcast1] at h1
  linear_combination 24*hc + (1)*h0 + (-5)*h1
#print axioms scaled_count_5_2_1

theorem scaled_count_5_2_2 (p : ℕ) (hp : 5 < p) :
    24*(carryCount p 5 2 2:ℤ) = (6)*(p:ℤ)^1 + (1)*(p:ℤ)^2 + (6)*(p:ℤ)^3 + (11)*(p:ℤ)^4 := by
  have hc : (carryCount p 5 2 2:ℤ)=(1)*((4+(2*p-2-p*0)).choose 4:ℤ) + (-5)*((4+(2*p-2-p*1)).choose 4:ℤ) := by
    rw [count_formula ℤ p 5 2 2 hp (by omega) (by omega) (by omega) (by omega)]
    norm_num [Finset.sum_range_succ, (show (5:ℕ).choose 0=1 from by decide), (show (5:ℕ).choose 1=5 from by decide), (show (5:ℕ).choose 2=10 from by decide), (show (5:ℕ).choose 3=10 from by decide), (show (5:ℕ).choose 4=5 from by decide), (show (5:ℕ).choose 5=1 from by decide)]
  have hn0 : (2*p-2-p*0)+2+p*0=2*p := by omega
  have hcast0 : (((2*p-2-p*0):ℕ):ℤ)=(2:ℤ)*p-2-p*0 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn0
    push_cast at ht
    linarith
  have h0 := choose_four_shift (2*p-2-p*0)
  rw [hcast0] at h0
  have hn1 : (2*p-2-p*1)+2+p*1=2*p := by omega
  have hcast1 : (((2*p-2-p*1):ℕ):ℤ)=(2:ℤ)*p-2-p*1 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn1
    push_cast at ht
    linarith
  have h1 := choose_four_shift (2*p-2-p*1)
  rw [hcast1] at h1
  linear_combination 24*hc + (1)*h0 + (-5)*h1
#print axioms scaled_count_5_2_2

theorem scaled_count_5_2_3 (p : ℕ) (hp : 5 < p) :
    24*(carryCount p 5 2 3:ℤ) = (-6)*(p:ℤ)^1 + (1)*(p:ℤ)^2 + (-6)*(p:ℤ)^3 + (11)*(p:ℤ)^4 := by
  have hc : (carryCount p 5 2 3:ℤ)=(1)*((4+(2*p-3-p*0)).choose 4:ℤ) + (-5)*((4+(2*p-3-p*1)).choose 4:ℤ) := by
    rw [count_formula ℤ p 5 2 3 hp (by omega) (by omega) (by omega) (by omega)]
    norm_num [Finset.sum_range_succ, (show (5:ℕ).choose 0=1 from by decide), (show (5:ℕ).choose 1=5 from by decide), (show (5:ℕ).choose 2=10 from by decide), (show (5:ℕ).choose 3=10 from by decide), (show (5:ℕ).choose 4=5 from by decide), (show (5:ℕ).choose 5=1 from by decide)]
  have hn0 : (2*p-3-p*0)+3+p*0=2*p := by omega
  have hcast0 : (((2*p-3-p*0):ℕ):ℤ)=(2:ℤ)*p-3-p*0 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn0
    push_cast at ht
    linarith
  have h0 := choose_four_shift (2*p-3-p*0)
  rw [hcast0] at h0
  have hn1 : (2*p-3-p*1)+3+p*1=2*p := by omega
  have hcast1 : (((2*p-3-p*1):ℕ):ℤ)=(2:ℤ)*p-3-p*1 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn1
    push_cast at ht
    linarith
  have h1 := choose_four_shift (2*p-3-p*1)
  rw [hcast1] at h1
  linear_combination 24*hc + (1)*h0 + (-5)*h1
#print axioms scaled_count_5_2_3

theorem scaled_count_5_2_4 (p : ℕ) (hp : 5 < p) :
    24*(carryCount p 5 2 4:ℤ) = (18)*(p:ℤ)^1 + (-11)*(p:ℤ)^2 + (-18)*(p:ℤ)^3 + (11)*(p:ℤ)^4 := by
  have hc : (carryCount p 5 2 4:ℤ)=(1)*((4+(2*p-4-p*0)).choose 4:ℤ) + (-5)*((4+(2*p-4-p*1)).choose 4:ℤ) := by
    rw [count_formula ℤ p 5 2 4 hp (by omega) (by omega) (by omega) (by omega)]
    norm_num [Finset.sum_range_succ, (show (5:ℕ).choose 0=1 from by decide), (show (5:ℕ).choose 1=5 from by decide), (show (5:ℕ).choose 2=10 from by decide), (show (5:ℕ).choose 3=10 from by decide), (show (5:ℕ).choose 4=5 from by decide), (show (5:ℕ).choose 5=1 from by decide)]
  have hn0 : (2*p-4-p*0)+4+p*0=2*p := by omega
  have hcast0 : (((2*p-4-p*0):ℕ):ℤ)=(2:ℤ)*p-4-p*0 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn0
    push_cast at ht
    linarith
  have h0 := choose_four_shift (2*p-4-p*0)
  rw [hcast0] at h0
  have hn1 : (2*p-4-p*1)+4+p*1=2*p := by omega
  have hcast1 : (((2*p-4-p*1):ℕ):ℤ)=(2:ℤ)*p-4-p*1 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn1
    push_cast at ht
    linarith
  have h1 := choose_four_shift (2*p-4-p*1)
  rw [hcast1] at h1
  linear_combination 24*hc + (1)*h0 + (-5)*h1
#print axioms scaled_count_5_2_4
end FiniteMT
```

### `Count5Row3.lean`

```lean
import CarryFormulaRange
import SmallChoose
namespace FiniteMT

theorem scaled_count_5_3_1 (p : ℕ) (hp : 5 < p) :
    24*(carryCount p 5 3 1:ℤ) = (18)*(p:ℤ)^1 + (-11)*(p:ℤ)^2 + (-18)*(p:ℤ)^3 + (11)*(p:ℤ)^4 := by
  have hc : (carryCount p 5 3 1:ℤ)=(1)*((4+(3*p-1-p*0)).choose 4:ℤ) + (-5)*((4+(3*p-1-p*1)).choose 4:ℤ) + (10)*((4+(3*p-1-p*2)).choose 4:ℤ) := by
    rw [count_formula ℤ p 5 3 1 hp (by omega) (by omega) (by omega) (by omega)]
    norm_num [Finset.sum_range_succ, (show (5:ℕ).choose 0=1 from by decide), (show (5:ℕ).choose 1=5 from by decide), (show (5:ℕ).choose 2=10 from by decide), (show (5:ℕ).choose 3=10 from by decide), (show (5:ℕ).choose 4=5 from by decide), (show (5:ℕ).choose 5=1 from by decide)]
  have hn0 : (3*p-1-p*0)+1+p*0=3*p := by omega
  have hcast0 : (((3*p-1-p*0):ℕ):ℤ)=(3:ℤ)*p-1-p*0 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn0
    push_cast at ht
    linarith
  have h0 := choose_four_shift (3*p-1-p*0)
  rw [hcast0] at h0
  have hn1 : (3*p-1-p*1)+1+p*1=3*p := by omega
  have hcast1 : (((3*p-1-p*1):ℕ):ℤ)=(3:ℤ)*p-1-p*1 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn1
    push_cast at ht
    linarith
  have h1 := choose_four_shift (3*p-1-p*1)
  rw [hcast1] at h1
  have hn2 : (3*p-1-p*2)+1+p*2=3*p := by omega
  have hcast2 : (((3*p-1-p*2):ℕ):ℤ)=(3:ℤ)*p-1-p*2 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn2
    push_cast at ht
    linarith
  have h2 := choose_four_shift (3*p-1-p*2)
  rw [hcast2] at h2
  linear_combination 24*hc + (1)*h0 + (-5)*h1 + (10)*h2
#print axioms scaled_count_5_3_1

theorem scaled_count_5_3_2 (p : ℕ) (hp : 5 < p) :
    24*(carryCount p 5 3 2:ℤ) = (-6)*(p:ℤ)^1 + (1)*(p:ℤ)^2 + (-6)*(p:ℤ)^3 + (11)*(p:ℤ)^4 := by
  have hc : (carryCount p 5 3 2:ℤ)=(1)*((4+(3*p-2-p*0)).choose 4:ℤ) + (-5)*((4+(3*p-2-p*1)).choose 4:ℤ) + (10)*((4+(3*p-2-p*2)).choose 4:ℤ) := by
    rw [count_formula ℤ p 5 3 2 hp (by omega) (by omega) (by omega) (by omega)]
    norm_num [Finset.sum_range_succ, (show (5:ℕ).choose 0=1 from by decide), (show (5:ℕ).choose 1=5 from by decide), (show (5:ℕ).choose 2=10 from by decide), (show (5:ℕ).choose 3=10 from by decide), (show (5:ℕ).choose 4=5 from by decide), (show (5:ℕ).choose 5=1 from by decide)]
  have hn0 : (3*p-2-p*0)+2+p*0=3*p := by omega
  have hcast0 : (((3*p-2-p*0):ℕ):ℤ)=(3:ℤ)*p-2-p*0 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn0
    push_cast at ht
    linarith
  have h0 := choose_four_shift (3*p-2-p*0)
  rw [hcast0] at h0
  have hn1 : (3*p-2-p*1)+2+p*1=3*p := by omega
  have hcast1 : (((3*p-2-p*1):ℕ):ℤ)=(3:ℤ)*p-2-p*1 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn1
    push_cast at ht
    linarith
  have h1 := choose_four_shift (3*p-2-p*1)
  rw [hcast1] at h1
  have hn2 : (3*p-2-p*2)+2+p*2=3*p := by omega
  have hcast2 : (((3*p-2-p*2):ℕ):ℤ)=(3:ℤ)*p-2-p*2 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn2
    push_cast at ht
    linarith
  have h2 := choose_four_shift (3*p-2-p*2)
  rw [hcast2] at h2
  linear_combination 24*hc + (1)*h0 + (-5)*h1 + (10)*h2
#print axioms scaled_count_5_3_2

theorem scaled_count_5_3_3 (p : ℕ) (hp : 5 < p) :
    24*(carryCount p 5 3 3:ℤ) = (6)*(p:ℤ)^1 + (1)*(p:ℤ)^2 + (6)*(p:ℤ)^3 + (11)*(p:ℤ)^4 := by
  have hc : (carryCount p 5 3 3:ℤ)=(1)*((4+(3*p-3-p*0)).choose 4:ℤ) + (-5)*((4+(3*p-3-p*1)).choose 4:ℤ) + (10)*((4+(3*p-3-p*2)).choose 4:ℤ) := by
    rw [count_formula ℤ p 5 3 3 hp (by omega) (by omega) (by omega) (by omega)]
    norm_num [Finset.sum_range_succ, (show (5:ℕ).choose 0=1 from by decide), (show (5:ℕ).choose 1=5 from by decide), (show (5:ℕ).choose 2=10 from by decide), (show (5:ℕ).choose 3=10 from by decide), (show (5:ℕ).choose 4=5 from by decide), (show (5:ℕ).choose 5=1 from by decide)]
  have hn0 : (3*p-3-p*0)+3+p*0=3*p := by omega
  have hcast0 : (((3*p-3-p*0):ℕ):ℤ)=(3:ℤ)*p-3-p*0 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn0
    push_cast at ht
    linarith
  have h0 := choose_four_shift (3*p-3-p*0)
  rw [hcast0] at h0
  have hn1 : (3*p-3-p*1)+3+p*1=3*p := by omega
  have hcast1 : (((3*p-3-p*1):ℕ):ℤ)=(3:ℤ)*p-3-p*1 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn1
    push_cast at ht
    linarith
  have h1 := choose_four_shift (3*p-3-p*1)
  rw [hcast1] at h1
  have hn2 : (3*p-3-p*2)+3+p*2=3*p := by omega
  have hcast2 : (((3*p-3-p*2):ℕ):ℤ)=(3:ℤ)*p-3-p*2 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn2
    push_cast at ht
    linarith
  have h2 := choose_four_shift (3*p-3-p*2)
  rw [hcast2] at h2
  linear_combination 24*hc + (1)*h0 + (-5)*h1 + (10)*h2
#print axioms scaled_count_5_3_3

theorem scaled_count_5_3_4 (p : ℕ) (hp : 5 < p) :
    24*(carryCount p 5 3 4:ℤ) = (-18)*(p:ℤ)^1 + (-11)*(p:ℤ)^2 + (18)*(p:ℤ)^3 + (11)*(p:ℤ)^4 := by
  have hc : (carryCount p 5 3 4:ℤ)=(1)*((4+(3*p-4-p*0)).choose 4:ℤ) + (-5)*((4+(3*p-4-p*1)).choose 4:ℤ) + (10)*((4+(3*p-4-p*2)).choose 4:ℤ) := by
    rw [count_formula ℤ p 5 3 4 hp (by omega) (by omega) (by omega) (by omega)]
    norm_num [Finset.sum_range_succ, (show (5:ℕ).choose 0=1 from by decide), (show (5:ℕ).choose 1=5 from by decide), (show (5:ℕ).choose 2=10 from by decide), (show (5:ℕ).choose 3=10 from by decide), (show (5:ℕ).choose 4=5 from by decide), (show (5:ℕ).choose 5=1 from by decide)]
  have hn0 : (3*p-4-p*0)+4+p*0=3*p := by omega
  have hcast0 : (((3*p-4-p*0):ℕ):ℤ)=(3:ℤ)*p-4-p*0 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn0
    push_cast at ht
    linarith
  have h0 := choose_four_shift (3*p-4-p*0)
  rw [hcast0] at h0
  have hn1 : (3*p-4-p*1)+4+p*1=3*p := by omega
  have hcast1 : (((3*p-4-p*1):ℕ):ℤ)=(3:ℤ)*p-4-p*1 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn1
    push_cast at ht
    linarith
  have h1 := choose_four_shift (3*p-4-p*1)
  rw [hcast1] at h1
  have hn2 : (3*p-4-p*2)+4+p*2=3*p := by omega
  have hcast2 : (((3*p-4-p*2):ℕ):ℤ)=(3:ℤ)*p-4-p*2 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn2
    push_cast at ht
    linarith
  have h2 := choose_four_shift (3*p-4-p*2)
  rw [hcast2] at h2
  linear_combination 24*hc + (1)*h0 + (-5)*h1 + (10)*h2
#print axioms scaled_count_5_3_4
end FiniteMT
```

### `Count5Row4.lean`

```lean
import CarryFormulaRange
import SmallChoose
namespace FiniteMT

theorem scaled_count_5_4_1 (p : ℕ) (hp : 5 < p) :
    24*(carryCount p 5 4 1:ℤ) = (-6)*(p:ℤ)^1 + (11)*(p:ℤ)^2 + (-6)*(p:ℤ)^3 + (1)*(p:ℤ)^4 := by
  have hc : (carryCount p 5 4 1:ℤ)=(1)*((4+(4*p-1-p*0)).choose 4:ℤ) + (-5)*((4+(4*p-1-p*1)).choose 4:ℤ) + (10)*((4+(4*p-1-p*2)).choose 4:ℤ) + (-10)*((4+(4*p-1-p*3)).choose 4:ℤ) := by
    rw [count_formula ℤ p 5 4 1 hp (by omega) (by omega) (by omega) (by omega)]
    norm_num [Finset.sum_range_succ, (show (5:ℕ).choose 0=1 from by decide), (show (5:ℕ).choose 1=5 from by decide), (show (5:ℕ).choose 2=10 from by decide), (show (5:ℕ).choose 3=10 from by decide), (show (5:ℕ).choose 4=5 from by decide), (show (5:ℕ).choose 5=1 from by decide)]
  have hn0 : (4*p-1-p*0)+1+p*0=4*p := by omega
  have hcast0 : (((4*p-1-p*0):ℕ):ℤ)=(4:ℤ)*p-1-p*0 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn0
    push_cast at ht
    linarith
  have h0 := choose_four_shift (4*p-1-p*0)
  rw [hcast0] at h0
  have hn1 : (4*p-1-p*1)+1+p*1=4*p := by omega
  have hcast1 : (((4*p-1-p*1):ℕ):ℤ)=(4:ℤ)*p-1-p*1 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn1
    push_cast at ht
    linarith
  have h1 := choose_four_shift (4*p-1-p*1)
  rw [hcast1] at h1
  have hn2 : (4*p-1-p*2)+1+p*2=4*p := by omega
  have hcast2 : (((4*p-1-p*2):ℕ):ℤ)=(4:ℤ)*p-1-p*2 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn2
    push_cast at ht
    linarith
  have h2 := choose_four_shift (4*p-1-p*2)
  rw [hcast2] at h2
  have hn3 : (4*p-1-p*3)+1+p*3=4*p := by omega
  have hcast3 : (((4*p-1-p*3):ℕ):ℤ)=(4:ℤ)*p-1-p*3 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn3
    push_cast at ht
    linarith
  have h3 := choose_four_shift (4*p-1-p*3)
  rw [hcast3] at h3
  linear_combination 24*hc + (1)*h0 + (-5)*h1 + (10)*h2 + (-10)*h3
#print axioms scaled_count_5_4_1

theorem scaled_count_5_4_2 (p : ℕ) (hp : 5 < p) :
    24*(carryCount p 5 4 2:ℤ) = (2)*(p:ℤ)^1 + (-1)*(p:ℤ)^2 + (-2)*(p:ℤ)^3 + (1)*(p:ℤ)^4 := by
  have hc : (carryCount p 5 4 2:ℤ)=(1)*((4+(4*p-2-p*0)).choose 4:ℤ) + (-5)*((4+(4*p-2-p*1)).choose 4:ℤ) + (10)*((4+(4*p-2-p*2)).choose 4:ℤ) + (-10)*((4+(4*p-2-p*3)).choose 4:ℤ) := by
    rw [count_formula ℤ p 5 4 2 hp (by omega) (by omega) (by omega) (by omega)]
    norm_num [Finset.sum_range_succ, (show (5:ℕ).choose 0=1 from by decide), (show (5:ℕ).choose 1=5 from by decide), (show (5:ℕ).choose 2=10 from by decide), (show (5:ℕ).choose 3=10 from by decide), (show (5:ℕ).choose 4=5 from by decide), (show (5:ℕ).choose 5=1 from by decide)]
  have hn0 : (4*p-2-p*0)+2+p*0=4*p := by omega
  have hcast0 : (((4*p-2-p*0):ℕ):ℤ)=(4:ℤ)*p-2-p*0 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn0
    push_cast at ht
    linarith
  have h0 := choose_four_shift (4*p-2-p*0)
  rw [hcast0] at h0
  have hn1 : (4*p-2-p*1)+2+p*1=4*p := by omega
  have hcast1 : (((4*p-2-p*1):ℕ):ℤ)=(4:ℤ)*p-2-p*1 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn1
    push_cast at ht
    linarith
  have h1 := choose_four_shift (4*p-2-p*1)
  rw [hcast1] at h1
  have hn2 : (4*p-2-p*2)+2+p*2=4*p := by omega
  have hcast2 : (((4*p-2-p*2):ℕ):ℤ)=(4:ℤ)*p-2-p*2 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn2
    push_cast at ht
    linarith
  have h2 := choose_four_shift (4*p-2-p*2)
  rw [hcast2] at h2
  have hn3 : (4*p-2-p*3)+2+p*3=4*p := by omega
  have hcast3 : (((4*p-2-p*3):ℕ):ℤ)=(4:ℤ)*p-2-p*3 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn3
    push_cast at ht
    linarith
  have h3 := choose_four_shift (4*p-2-p*3)
  rw [hcast3] at h3
  linear_combination 24*hc + (1)*h0 + (-5)*h1 + (10)*h2 + (-10)*h3
#print axioms scaled_count_5_4_2

theorem scaled_count_5_4_3 (p : ℕ) (hp : 5 < p) :
    24*(carryCount p 5 4 3:ℤ) = (-2)*(p:ℤ)^1 + (-1)*(p:ℤ)^2 + (2)*(p:ℤ)^3 + (1)*(p:ℤ)^4 := by
  have hc : (carryCount p 5 4 3:ℤ)=(1)*((4+(4*p-3-p*0)).choose 4:ℤ) + (-5)*((4+(4*p-3-p*1)).choose 4:ℤ) + (10)*((4+(4*p-3-p*2)).choose 4:ℤ) + (-10)*((4+(4*p-3-p*3)).choose 4:ℤ) := by
    rw [count_formula ℤ p 5 4 3 hp (by omega) (by omega) (by omega) (by omega)]
    norm_num [Finset.sum_range_succ, (show (5:ℕ).choose 0=1 from by decide), (show (5:ℕ).choose 1=5 from by decide), (show (5:ℕ).choose 2=10 from by decide), (show (5:ℕ).choose 3=10 from by decide), (show (5:ℕ).choose 4=5 from by decide), (show (5:ℕ).choose 5=1 from by decide)]
  have hn0 : (4*p-3-p*0)+3+p*0=4*p := by omega
  have hcast0 : (((4*p-3-p*0):ℕ):ℤ)=(4:ℤ)*p-3-p*0 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn0
    push_cast at ht
    linarith
  have h0 := choose_four_shift (4*p-3-p*0)
  rw [hcast0] at h0
  have hn1 : (4*p-3-p*1)+3+p*1=4*p := by omega
  have hcast1 : (((4*p-3-p*1):ℕ):ℤ)=(4:ℤ)*p-3-p*1 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn1
    push_cast at ht
    linarith
  have h1 := choose_four_shift (4*p-3-p*1)
  rw [hcast1] at h1
  have hn2 : (4*p-3-p*2)+3+p*2=4*p := by omega
  have hcast2 : (((4*p-3-p*2):ℕ):ℤ)=(4:ℤ)*p-3-p*2 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn2
    push_cast at ht
    linarith
  have h2 := choose_four_shift (4*p-3-p*2)
  rw [hcast2] at h2
  have hn3 : (4*p-3-p*3)+3+p*3=4*p := by omega
  have hcast3 : (((4*p-3-p*3):ℕ):ℤ)=(4:ℤ)*p-3-p*3 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn3
    push_cast at ht
    linarith
  have h3 := choose_four_shift (4*p-3-p*3)
  rw [hcast3] at h3
  linear_combination 24*hc + (1)*h0 + (-5)*h1 + (10)*h2 + (-10)*h3
#print axioms scaled_count_5_4_3

theorem scaled_count_5_4_4 (p : ℕ) (hp : 5 < p) :
    24*(carryCount p 5 4 4:ℤ) = (6)*(p:ℤ)^1 + (11)*(p:ℤ)^2 + (6)*(p:ℤ)^3 + (1)*(p:ℤ)^4 := by
  have hc : (carryCount p 5 4 4:ℤ)=(1)*((4+(4*p-4-p*0)).choose 4:ℤ) + (-5)*((4+(4*p-4-p*1)).choose 4:ℤ) + (10)*((4+(4*p-4-p*2)).choose 4:ℤ) + (-10)*((4+(4*p-4-p*3)).choose 4:ℤ) := by
    rw [count_formula ℤ p 5 4 4 hp (by omega) (by omega) (by omega) (by omega)]
    norm_num [Finset.sum_range_succ, (show (5:ℕ).choose 0=1 from by decide), (show (5:ℕ).choose 1=5 from by decide), (show (5:ℕ).choose 2=10 from by decide), (show (5:ℕ).choose 3=10 from by decide), (show (5:ℕ).choose 4=5 from by decide), (show (5:ℕ).choose 5=1 from by decide)]
  have hn0 : (4*p-4-p*0)+4+p*0=4*p := by omega
  have hcast0 : (((4*p-4-p*0):ℕ):ℤ)=(4:ℤ)*p-4-p*0 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn0
    push_cast at ht
    linarith
  have h0 := choose_four_shift (4*p-4-p*0)
  rw [hcast0] at h0
  have hn1 : (4*p-4-p*1)+4+p*1=4*p := by omega
  have hcast1 : (((4*p-4-p*1):ℕ):ℤ)=(4:ℤ)*p-4-p*1 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn1
    push_cast at ht
    linarith
  have h1 := choose_four_shift (4*p-4-p*1)
  rw [hcast1] at h1
  have hn2 : (4*p-4-p*2)+4+p*2=4*p := by omega
  have hcast2 : (((4*p-4-p*2):ℕ):ℤ)=(4:ℤ)*p-4-p*2 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn2
    push_cast at ht
    linarith
  have h2 := choose_four_shift (4*p-4-p*2)
  rw [hcast2] at h2
  have hn3 : (4*p-4-p*3)+4+p*3=4*p := by omega
  have hcast3 : (((4*p-4-p*3):ℕ):ℤ)=(4:ℤ)*p-4-p*3 := by
    have ht := congrArg (fun t : ℕ => (t:ℤ)) hn3
    push_cast at ht
    linarith
  have h3 := choose_four_shift (4*p-4-p*3)
  rw [hcast3] at h3
  linear_combination 24*hc + (1)*h0 + (-5)*h1 + (10)*h2 + (-10)*h3
#print axioms scaled_count_5_4_4
end FiniteMT
```

### `Count4Table.lean`

```lean
import Count4Row1
import Count4Row2
import Count4Row3
import Mathlib.Tactic.FinCases
namespace FiniteMT
noncomputable section

def scaledMatrix4 {R : Type*} [CommRing R] (q : R) : Fin 3 → Fin 3 → R :=
  ![![(2)*q^1 + (3)*q^2 + (1)*q^3,(-1)*q^1 + (1)*q^3,(2)*q^1 + (-3)*q^2 + (1)*q^3],
    ![(-4)*q^1 + (4)*q^3,(2)*q^1 + (4)*q^3,(-4)*q^1 + (4)*q^3],
    ![(2)*q^1 + (-3)*q^2 + (1)*q^3,(-1)*q^1 + (1)*q^3,(2)*q^1 + (3)*q^2 + (1)*q^3]]

theorem scaled_count4 (R : Type*) [CommRing R] (p : ℕ) (hp : 4 < p) (a b : Fin 3) :
    6*(carryCount p 4 (a.val+1) (b.val+1):R)=scaledMatrix4 (p:R) a b := by
  fin_cases a <;> fin_cases b
  · have ht := congrArg (Int.castRingHom R) (scaled_count_4_1_1 p hp)
    simpa [scaledMatrix4] using ht
  · have ht := congrArg (Int.castRingHom R) (scaled_count_4_1_2 p hp)
    simpa [scaledMatrix4] using ht
  · have ht := congrArg (Int.castRingHom R) (scaled_count_4_1_3 p hp)
    simpa [scaledMatrix4] using ht
  · have ht := congrArg (Int.castRingHom R) (scaled_count_4_2_1 p hp)
    simpa [scaledMatrix4] using ht
  · have ht := congrArg (Int.castRingHom R) (scaled_count_4_2_2 p hp)
    simpa [scaledMatrix4] using ht
  · have ht := congrArg (Int.castRingHom R) (scaled_count_4_2_3 p hp)
    simpa [scaledMatrix4] using ht
  · have ht := congrArg (Int.castRingHom R) (scaled_count_4_3_1 p hp)
    simpa [scaledMatrix4] using ht
  · have ht := congrArg (Int.castRingHom R) (scaled_count_4_3_2 p hp)
    simpa [scaledMatrix4] using ht
  · have ht := congrArg (Int.castRingHom R) (scaled_count_4_3_3 p hp)
    simpa [scaledMatrix4] using ht

#print axioms scaled_count4
end
end FiniteMT
```

### `Count5Table.lean`

```lean
import Count5Row1
import Count5Row2
import Count5Row3
import Count5Row4
import Mathlib.Tactic.FinCases
namespace FiniteMT
noncomputable section

def scaledMatrix5 {R : Type*} [CommRing R] (q : R) : Fin 4 → Fin 4 → R :=
  ![![(6)*q^1 + (11)*q^2 + (6)*q^3 + (1)*q^4,(-2)*q^1 + (-1)*q^2 + (2)*q^3 + (1)*q^4,(2)*q^1 + (-1)*q^2 + (-2)*q^3 + (1)*q^4,(-6)*q^1 + (11)*q^2 + (-6)*q^3 + (1)*q^4],
    ![(-18)*q^1 + (-11)*q^2 + (18)*q^3 + (11)*q^4,(6)*q^1 + (1)*q^2 + (6)*q^3 + (11)*q^4,(-6)*q^1 + (1)*q^2 + (-6)*q^3 + (11)*q^4,(18)*q^1 + (-11)*q^2 + (-18)*q^3 + (11)*q^4],
    ![(18)*q^1 + (-11)*q^2 + (-18)*q^3 + (11)*q^4,(-6)*q^1 + (1)*q^2 + (-6)*q^3 + (11)*q^4,(6)*q^1 + (1)*q^2 + (6)*q^3 + (11)*q^4,(-18)*q^1 + (-11)*q^2 + (18)*q^3 + (11)*q^4],
    ![(-6)*q^1 + (11)*q^2 + (-6)*q^3 + (1)*q^4,(2)*q^1 + (-1)*q^2 + (-2)*q^3 + (1)*q^4,(-2)*q^1 + (-1)*q^2 + (2)*q^3 + (1)*q^4,(6)*q^1 + (11)*q^2 + (6)*q^3 + (1)*q^4]]

theorem scaled_count5 (R : Type*) [CommRing R] (p : ℕ) (hp : 5 < p) (a b : Fin 4) :
    24*(carryCount p 5 (a.val+1) (b.val+1):R)=scaledMatrix5 (p:R) a b := by
  fin_cases a <;> fin_cases b
  · have ht := congrArg (Int.castRingHom R) (scaled_count_5_1_1 p hp)
    simpa [scaledMatrix5] using ht
  · have ht := congrArg (Int.castRingHom R) (scaled_count_5_1_2 p hp)
    simpa [scaledMatrix5] using ht
  · have ht := congrArg (Int.castRingHom R) (scaled_count_5_1_3 p hp)
    simpa [scaledMatrix5] using ht
  · have ht := congrArg (Int.castRingHom R) (scaled_count_5_1_4 p hp)
    simpa [scaledMatrix5] using ht
  · have ht := congrArg (Int.castRingHom R) (scaled_count_5_2_1 p hp)
    simpa [scaledMatrix5] using ht
  · have ht := congrArg (Int.castRingHom R) (scaled_count_5_2_2 p hp)
    simpa [scaledMatrix5] using ht
  · have ht := congrArg (Int.castRingHom R) (scaled_count_5_2_3 p hp)
    simpa [scaledMatrix5] using ht
  · have ht := congrArg (Int.castRingHom R) (scaled_count_5_2_4 p hp)
    simpa [scaledMatrix5] using ht
  · have ht := congrArg (Int.castRingHom R) (scaled_count_5_3_1 p hp)
    simpa [scaledMatrix5] using ht
  · have ht := congrArg (Int.castRingHom R) (scaled_count_5_3_2 p hp)
    simpa [scaledMatrix5] using ht
  · have ht := congrArg (Int.castRingHom R) (scaled_count_5_3_3 p hp)
    simpa [scaledMatrix5] using ht
  · have ht := congrArg (Int.castRingHom R) (scaled_count_5_3_4 p hp)
    simpa [scaledMatrix5] using ht
  · have ht := congrArg (Int.castRingHom R) (scaled_count_5_4_1 p hp)
    simpa [scaledMatrix5] using ht
  · have ht := congrArg (Int.castRingHom R) (scaled_count_5_4_2 p hp)
    simpa [scaledMatrix5] using ht
  · have ht := congrArg (Int.castRingHom R) (scaled_count_5_4_3 p hp)
    simpa [scaledMatrix5] using ht
  · have ht := congrArg (Int.castRingHom R) (scaled_count_5_4_4 p hp)
    simpa [scaledMatrix5] using ht

#print axioms scaled_count5
end
end FiniteMT
```

### `ModeAlgebra4.lean`

```lean
import Count4Table
import MatrixProjection
open scoped BigOperators
noncomputable section
namespace FiniteMT

theorem matrix4minus {R : Type*} [CommRing R] (q half : R) (v : Fin 3 → R) (a : Fin 3) :
    matrixAction (scaledMatrix4 q) (parityProjection half (-1) v) a =
      6*q^2*parityProjection half (-1) v a := by
  fin_cases a <;> norm_num [matrixAction, scaledMatrix4, parityProjection, Fin.sum_univ_succ, Fin.rev] <;> ring

theorem matrix4plus {R : Type*} [CommRing R] (q half : R) (hh : half*2=1)
    (v : Fin 3 → R) (a : Fin 3) :
    matrixAction (scaledMatrix4 q) (parityProjection half 1 v) a =
      6*q*parityProjection half 1 v a+(q^3-q)*(∑ b, v b)*(![1,4,1] a) := by
  fin_cases a
  · norm_num [matrixAction, scaledMatrix4, parityProjection, Fin.sum_univ_succ, Fin.rev]
    linear_combination (q^3-q)*(v 0+v 1+v 2)*hh
  · norm_num [matrixAction, scaledMatrix4, parityProjection, Fin.sum_univ_succ, Fin.rev]
    linear_combination 4*(q^3-q)*(v 0+v 1+v 2)*hh
  · norm_num [matrixAction, scaledMatrix4, parityProjection, Fin.sum_univ_succ, Fin.rev]
    linear_combination (q^3-q)*(v 0+v 1+v 2)*hh

#print axioms matrix4minus
#print axioms matrix4plus
end FiniteMT
```

### `ModeAlgebra5.lean`

```lean
import Count5Table
import MatrixProjection
open scoped BigOperators
noncomputable section
namespace FiniteMT

theorem matrix5plus {R : Type*} [CommRing R] (q half : R) (hh : half*2=1)
    (v : Fin 4 → R) (a : Fin 4) :
    matrixAction (scaledMatrix5 q) (parityProjection half 1 v) a =
      24*q^2*parityProjection half 1 v a+(q^4-q^2)*(∑ b, v b)*(![1,11,11,1] a) := by
  fin_cases a
  · norm_num [matrixAction, scaledMatrix5, parityProjection, Fin.sum_univ_succ, Fin.rev]
    linear_combination (q^4-q^2)*(v 0+v 1+v 2+v 3)*hh
  · norm_num [matrixAction, scaledMatrix5, parityProjection, Fin.sum_univ_succ, Fin.rev]
    linear_combination 11*(q^4-q^2)*(v 0+v 1+v 2+v 3)*hh
  · norm_num [matrixAction, scaledMatrix5, parityProjection, Fin.sum_univ_succ, Fin.rev]
    linear_combination 11*(q^4-q^2)*(v 0+v 1+v 2+v 3)*hh
  · norm_num [matrixAction, scaledMatrix5, parityProjection, Fin.sum_univ_succ, Fin.rev]
    linear_combination (q^4-q^2)*(v 0+v 1+v 2+v 3)*hh

#print axioms matrix5plus
end FiniteMT
```

### `TotalInduction.lean`

```lean
import InitialCarry
import StrongDivisibility
open scoped BigOperators
noncomputable section
namespace FiniteMT

def carryTotal (p r k : ℕ) {d : ℕ} (s : Fin d → ℕ) : ZMod (p^k) :=
  ∑ b : Fin (d-1), carrySum p r k s (b.val+1)

theorem reduce_carryTotal (p r k l d : ℕ) (s : Fin d → ℕ) (hp : p.Prime) (hkl : k ≤ l) :
    ZMod.castHom (pow_dvd_pow p hkl) (ZMod (p^k)) (carryTotal p r l s)=carryTotal p r k s := by
  simp only [carryTotal, map_sum, reduce_carrySum p r k l s _ hp hkl]

theorem carryTotal_dvd_of_zero (p r e k d : ℕ) (s : Fin d → ℕ) (hp : p.Prime)
    (hz : carryTotal p r e s=0) : (p:ZMod (p^k))^e ∣ carryTotal p r k s := by
  by_cases hk : e ≤ k
  · apply (reduction_zero_iff p e k hp hk _).mp
    rw [reduce_carryTotal p r e k d s hp hk, hz]
  · have hke : k ≤ e := by omega
    have ht := congrArg (ZMod.castHom (pow_dvd_pow p hke) (ZMod (p^k))) hz
    rw [reduce_carryTotal p r k e d s hp hke, map_zero] at ht
    rw [ht]
    exact dvd_zero _

/-- A common induction for the exceptional total modes. -/
theorem carryTotal_induction (p d e f : ℕ) (s : Fin d → ℕ) (hp : p.Prime)
    (hef : e ≤ f) (hbase : carryTotal p 1 1 s=0)
    (hrec : ∀ r, 1 ≤ r → carryTotal p (r+1) (e*r+1) s =
      (p:ZMod (p^(e*r+1)))^f*carryTotal p r (e*r+1) s) :
    ∀ r, 1 ≤ r → ∀ k, (p:ZMod (p^k))^(e*(r-1)+1) ∣ carryTotal p r k s := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
    intro k
    simpa using carryTotal_dvd_of_zero p 1 1 k d s hp hbase
  | succ r hr ih =>
    intro k
    have hz : carryTotal p (r+1) (e*r+1) s=0 := by
      rw [hrec r hr]
      obtain ⟨q,hq⟩ := ih (e*r+1)
      rw [hq, ← mul_assoc, ← pow_add]
      rw [ZMod.natCast_pow_eq_zero_of_le p (by
        have he : e*r=e*(r-1)+e := by
          conv_lhs => rw [← Nat.sub_add_cancel hr, Nat.mul_add, Nat.mul_one]
        omega), zero_mul]
    simpa using carryTotal_dvd_of_zero p (r+1) (e*r+1) k d s hp hz

/-- Promotion from an exact equality at the defining precision to the shared
scalar recurrence at every ambient precision. -/
theorem scalarRecurrence_of_exact (p d e : ℕ) (s : Fin d → ℕ) (hp : p.Prime)
    (hex : ∀ r, 1 ≤ r → ∀ a, 1 ≤ a → a < d →
      carrySum p (r+1) (e*r+1) s a=
        (p:ZMod (p^(e*r+1)))^e*carrySum p r (e*r+1) s a) :
    ScalarCarryRecurrence p d e s := by
  intro r hr k a ha had
  let n := e*r+1
  have hz : carrySum p (r+1) n s a-(p:ZMod (p^n))^e*carrySum p r n s a=0 :=
    sub_eq_zero.mpr (hex r hr a ha had)
  by_cases hk : n ≤ k
  · apply (reduction_zero_iff p n k hp hk _).mp
    simpa only [map_sub, map_mul, map_pow, map_natCast,
      reduce_carrySum p _ n k s a hp hk] using hz
  · have hke : k ≤ n := by omega
    have ht := congrArg (ZMod.castHom (pow_dvd_pow p hke) (ZMod (p^k))) hz
    have he : carrySum p (r+1) k s a-(p:ZMod (p^k))^e*carrySum p r k s a=0 := by
      simpa only [map_sub, map_mul, map_pow, map_natCast, map_zero,
        reduce_carrySum p _ k n s a hp hke] using ht
    rw [he]
    exact dvd_zero _

#print axioms carryTotal_induction
#print axioms scalarRecurrence_of_exact
end FiniteMT
```

### `Modes4.lean`

```lean
import ModeAlgebra4
import ProjectedDerivative
open scoped BigOperators
noncomputable section
namespace FiniteMT

theorem small_unit (p k n : ℕ) (hp : p.Prime) (hn : ¬ p ∣ n) : IsUnit (n:ZMod (p^k)) := by
  by_cases hk : k=0
  · subst k
    let : Subsingleton (ZMod (p^0)) := ZMod.subsingleton_iff.mpr (pow_zero p)
    have he : (n:ZMod (p^0))=1 := Subsingleton.elim _ _
    rw [he]
    exact isUnit_one
  · exact Taylor.coordinate_isUnit p k n hp (by omega) hn

theorem six_unit (p k : ℕ) (hp : p.Prime) (hp3 : 3 < p) : IsUnit (6:ZMod (p^k)) := by
  have h2 := small_unit p k 2 hp (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  have h3 := small_unit p k 3 hp (Nat.not_dvd_of_pos_of_lt (by decide) hp3)
  convert h2.mul h3 using 1
  norm_num

theorem scaled_carryAction4 (p k : ℕ) (hp : 4 < p) (v : Fin 3 → ZMod (p^k)) (a : Fin 3) :
    6*carryAction p 4 k v (a.val+1)=matrixAction (scaledMatrix4 (p:ZMod (p^k))) v a := by
  unfold carryAction matrixAction
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [← mul_assoc, scaled_count4 (ZMod (p^k)) p hp a b]

theorem mode4minus (p k : ℕ) (hp : p.Prime) (hp4 : 4 < p)
    (v : Fin 3 → ZMod (p^k)) (a : Fin 3) :
    carryAction p 4 k (parityProjection (2:ZMod (p^k))⁻¹ (-1) v) (a.val+1)=
      (p:ZMod (p^k))^2*parityProjection (2:ZMod (p^k))⁻¹ (-1) v a := by
  apply (six_unit p k hp (by omega)).mul_left_cancel
  rw [scaled_carryAction4 p k hp4, matrix4minus]
  ring

theorem mode4plus (p k : ℕ) (hp : p.Prime) (hp4 : 4 < p)
    (v : Fin 3 → ZMod (p^k)) (a : Fin 3) :
    carryAction p 4 k (parityProjection (2:ZMod (p^k))⁻¹ 1 v) (a.val+1)=
      (p:ZMod (p^k))*parityProjection (2:ZMod (p^k))⁻¹ 1 v a+
        (6:ZMod (p^k))⁻¹*((p:ZMod (p^k))^3-p)*(∑ b,v b)*(![1,4,1] a) := by
  apply (six_unit p k hp (by omega)).mul_left_cancel
  rw [scaled_carryAction4 p k hp4, matrix4plus _ _ (half_mul_two p k hp (by omega))]
  have hi : (6:ZMod (p^k))*(6:ZMod (p^k))⁻¹=1 :=
    ZMod.mul_inv_of_unit _ (six_unit p k hp (by omega))
  linear_combination -((p:ZMod (p^k))^3-p)*(∑ b,v b)*(![1,4,1] a)*hi

#print axioms mode4minus
#print axioms mode4plus
end FiniteMT
```

### `Assertion12.lean`

```lean
import Modes4
import TotalInduction
namespace FiniteMT
noncomputable section

theorem scalarRecurrence12 (p : ℕ) (s : Fin 4 → ℕ) (hp : p.Prime)
    (hp4 : 5 < p) (ho : Odd (weight s)) : ScalarCarryRecurrence p 4 2 s := by
  apply scalarRecurrence_of_exact p 4 2 s hp
  intro r hr a ha had
  have hot : Odd (4+weight s) := by
    apply Nat.odd_iff.mpr
    have := Nat.odd_iff.mp ho
    omega
  have hl := projectedCarryLift p r 4 s hp hr (by decide) hp4 hot a ha had
  rw [ho.neg_one_pow] at hl
  let b : Fin 3 := ⟨a-1, by omega⟩
  have hb : b.val+1=a := by dsimp [b]; omega
  have hm := mode4minus p (2*r+1) hp (by omega)
    (fun b => carrySum p r (2*r+1) s (b.val+1)) b
  rw [hb] at hm
  rw [hl, hm]
  have ht := wrongParity_project_dvd p r (2*r+1) 4 a s hp hr hp4 ha had
  rw [ho.neg_one_pow] at ht
  obtain ⟨q,hq⟩ := ht
  have he : parityProjection (2:ZMod (p^(2*r+1)))⁻¹ (-1)
      (fun b : Fin 3 => carrySum p r (2*r+1) s (b.val+1)) b =
      carryProject p r (2*r+1) s (-1) a := by
    simp only [parityProjection, carryProject, (carry_rev_index (d:=4)), hb]
  rw [he]
  have hz : (p:ZMod (p^(2*r+1)))^2 *
      (carrySum p r (2*r+1) s a-carryProject p r (2*r+1) s (-1) a)=0 := by
    rw [hq, ← mul_assoc, ← pow_add]
    rw [ZMod.natCast_pow_eq_zero_of_le p (by omega), zero_mul]
  linear_combination -hz

theorem assertion12 : Scaling12 := by
  intro p r s hp hr hs hw ho
  have hdp : 5 < p := lt_of_le_of_lt
    (Nat.add_le_add_right (depth_le_weight s hs) 1) hw
  have ht := scalar_scaling p r 4 2 s hr (by decide) (scalarRecurrence12 p s hp hdp ho)
  have he1 : 2*(r-1)+1=2*r-1 := by omega
  have he2 : 2*(r-1)=2*r-2 := by omega
  rwa [he1, he2] at ht

#print axioms scalarRecurrence12
#print axioms assertion12
end
end FiniteMT
```

### `Modes5.lean`

```lean
import ModeAlgebra5
import Modes4
open scoped BigOperators
noncomputable section
namespace FiniteMT

theorem twentyfour_unit (p k : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    IsUnit (24:ZMod (p^k)) := by
  have h2 := small_unit p k 2 hp (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  have h3 := small_unit p k 3 hp (Nat.not_dvd_of_pos_of_lt (by decide) hp3)
  convert (h2.pow 3).mul h3 using 1
  norm_num

theorem scaled_carryAction5 (p k : ℕ) (hp : 5 < p) (v : Fin 4 → ZMod (p^k)) (a : Fin 4) :
    24*carryAction p 5 k v (a.val+1)=matrixAction (scaledMatrix5 (p:ZMod (p^k))) v a := by
  unfold carryAction matrixAction
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [← mul_assoc, scaled_count5 (ZMod (p^k)) p hp a b]

theorem mode5plus (p k : ℕ) (hp : p.Prime) (hp5 : 5 < p)
    (v : Fin 4 → ZMod (p^k)) (a : Fin 4) :
    carryAction p 5 k (parityProjection (2:ZMod (p^k))⁻¹ 1 v) (a.val+1)=
      (p:ZMod (p^k))^2*parityProjection (2:ZMod (p^k))⁻¹ 1 v a+
        (24:ZMod (p^k))⁻¹*((p:ZMod (p^k))^4-(p:ZMod (p^k))^2)*
          (∑ b,v b)*(![1,11,11,1] a) := by
  apply (twentyfour_unit p k hp (by omega)).mul_left_cancel
  rw [scaled_carryAction5 p k hp5, matrix5plus _ _ (half_mul_two p k hp (by omega))]
  have hi : (24:ZMod (p^k))*(24:ZMod (p^k))⁻¹=1 :=
    ZMod.mul_inv_of_unit _ (twentyfour_unit p k hp (by omega))
  linear_combination -((p:ZMod (p^k))^4-(p:ZMod (p^k))^2)*
    (∑ b,v b)*(![1,11,11,1] a)*hi

#print axioms mode5plus
end FiniteMT
```

### `CarryTotals.lean`

```lean
import Modes5
import TotalInduction
open scoped BigOperators
noncomputable section
namespace FiniteMT

theorem sum_projection_plus {R : Type*} [CommRing R] {n : ℕ} (half : R)
    (hh : half*2=1) (v : Fin n → R) : ∑ b, parityProjection half 1 v b=∑ b,v b := by
  simp only [parityProjection, one_mul]
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have he : (∑ b : Fin n,v b.rev)=∑ b,v b := Equiv.sum_comp Fin.revPerm v
  rw [he]
  linear_combination (∑ b,v b)*hh

theorem carryAction_total4 (p k : ℕ) (hp : p.Prime) (hp4 : 4 < p)
    (v : Fin 3 → ZMod (p^k)) :
    (∑ a : Fin 3, carryAction p 4 k v (a.val+1))=(p:ZMod (p^k))^3*∑ b,v b := by
  apply (six_unit p k hp (by omega)).mul_left_cancel
  rw [Finset.mul_sum]
  simp_rw [scaled_carryAction4 p k hp4]
  norm_num [matrixAction, scaledMatrix4, Fin.sum_univ_succ]
  ring

theorem carryAction_total5 (p k : ℕ) (hp : p.Prime) (hp5 : 5 < p)
    (v : Fin 4 → ZMod (p^k)) :
    (∑ a : Fin 4, carryAction p 5 k v (a.val+1))=(p:ZMod (p^k))^4*∑ b,v b := by
  apply (twentyfour_unit p k hp (by omega)).mul_left_cancel
  rw [Finset.mul_sum]
  simp_rw [scaled_carryAction5 p k hp5]
  norm_num [matrixAction, scaledMatrix5, Fin.sum_univ_succ]
  ring

theorem totalBound4 (p : ℕ) (s : Fin 4 → ℕ) (hp : p.Prime)
    (hs : ∀ i, 0 < s i) (hw : weight s+1 < p) :
    ∀ r, 1 ≤ r → ∀ k, (p:ZMod (p^k))^r ∣ carryTotal p r k s := by
  have hdp : 5 < p := lt_of_le_of_lt (Nat.add_le_add_right (depth_le_weight s hs) 1) hw
  have ht := carryTotal_induction p 4 1 3 s hp (by decide)
    (initialCarryCancellation p 4 s hp (by decide) hs hw) (by
      intro r hr
      have hrrec : carryTotal p (r+1) (r+1) s=
          (p:ZMod (p^(r+1)))^3*carryTotal p r (r+1) s := by
        unfold carryTotal
        have hl (a : Fin 3) : carrySum p (r+1) (r+1) s (a.val+1)=
            carryAction p 4 (r+1) (fun b => carrySum p r (r+1) s (b.val+1)) (a.val+1) :=
          carrySum_weak_plus p r 4 (a.val+1) s hp hr (by decide) hdp (by omega)
        simp_rw [hl]
        exact carryAction_total4 p (r+1) hp (by omega) _
      have haux (q : ℕ) (hq : q=r+1) : carryTotal p (r+1) q s=
          (p:ZMod (p^q))^3*carryTotal p r q s := by
        subst q
        exact hrrec
      exact haux (1*r+1) (by omega))
  intro r hr k
  simpa only [one_mul, Nat.sub_add_cancel hr] using ht r hr k

theorem totalBound5 (p : ℕ) (s : Fin 5 → ℕ) (hp : p.Prime)
    (hs : ∀ i, 0 < s i) (hw : weight s+1 < p) (he : Even (weight s)) :
    ∀ r, 1 ≤ r → ∀ k, (p:ZMod (p^k))^(2*r-1) ∣ carryTotal p r k s := by
  have hdp : 6 < p := lt_of_le_of_lt (Nat.add_le_add_right (depth_le_weight s hs) 1) hw
  have ho : Odd (5+weight s) := by
    apply Nat.odd_iff.mpr
    have := Nat.even_iff.mp he
    omega
  have ht := carryTotal_induction p 5 2 4 s hp (by decide)
    (initialCarryCancellation p 5 s hp (by decide) hs hw) (by
      intro r hr
      unfold carryTotal
      have hl (a : Fin 4) := projectedCarryLift p r 5 s hp hr (by decide) hdp ho
        (a.val+1) (by omega) (by have := a.isLt; omega)
      simp_rw [hl, he.neg_one_pow]
      rw [carryAction_total5 p (2*r+1) hp (by omega),
        sum_projection_plus _ (half_mul_two p (2*r+1) hp (by omega))])
  intro r hr k
  have hex : 2*(r-1)+1=2*r-1 := by omega
  simpa only [hex] using ht r hr k

#print axioms totalBound4
#print axioms totalBound5
end FiniteMT
```

### `PowerVanishing.lean`

```lean
import TotalInduction
namespace FiniteMT

theorem power_mul_zero (p k e f : ℕ) (x : ZMod (p^k))
    (hx : (p:ZMod (p^k))^f ∣ x) (h : k ≤ e+f) :
    (p:ZMod (p^k))^e*x=0 := by
  obtain ⟨q,hq⟩ := hx
  rw [hq, ← mul_assoc, ← pow_add, ZMod.natCast_pow_eq_zero_of_le p h, zero_mul]
end FiniteMT
```

### `Assertion14.lean`

```lean
import CarryTotals
import PowerVanishing
namespace FiniteMT
noncomputable section
open scoped BigOperators

theorem scalarRecurrence14 (p : ℕ) (s : Fin 5 → ℕ) (hp : p.Prime)
    (hs : ∀ i, 0 < s i) (hw : weight s+1 < p) (he : Even (weight s)) :
    ScalarCarryRecurrence p 5 2 s := by
  have hdp : 6 < p := lt_of_le_of_lt (Nat.add_le_add_right (depth_le_weight s hs) 1) hw
  apply scalarRecurrence_of_exact p 5 2 s hp
  intro r hr a ha had
  let A := ZMod (p^(2*r+1))
  let T : Fin 4 → A := fun b => carrySum p r (2*r+1) s (b.val+1)
  let b : Fin 4 := ⟨a-1,by omega⟩
  have hb : b.val+1=a := by dsimp [b]; omega
  have ho : Odd (5+weight s) := by
    apply Nat.odd_iff.mpr
    have := Nat.even_iff.mp he
    omega
  have hl := projectedCarryLift p r 5 s hp hr (by decide) hdp ho a ha had
  rw [he.neg_one_pow] at hl
  have hm := mode5plus p (2*r+1) hp (by omega) T b
  rw [hb] at hm
  have hP : parityProjection (2:A)⁻¹ 1 T b=carryProject p r (2*r+1) s 1 a := by
    simp only [parityProjection, carryProject, T, (carry_rev_index (d:=5)), hb]
  have hz1 := power_mul_zero p (2*r+1) 2 (2*r-1)
    (carrySum p r (2*r+1) s a-carryProject p r (2*r+1) s 1 a)
    (by simpa only [he.neg_one_pow] using
      wrongParity_project_dvd p r (2*r+1) 5 a s hp hr hdp ha had) (by omega)
  have hzS := power_mul_zero p (2*r+1) 2 (2*r-1) (carryTotal p r (2*r+1) s)
    (totalBound5 p s hp hs hw he r hr (2*r+1)) (by omega)
  change (p:A)^2*(∑ b,T b)=0 at hzS
  change carrySum p (r+1) (2*r+1) s a=(p:A)^2*carrySum p r (2*r+1) s a
  rw [hl]
  change carryAction p 5 (2*r+1) (parityProjection (2:A)⁻¹ 1 T) a=_
  rw [hm, hP]
  linear_combination -hz1+(24:A)⁻¹*((p:A)^2-1)*(![1,11,11,1] b)*hzS

theorem assertion14 : Scaling14 := by
  intro p r s hp hr hs hw he
  have ht := scalar_scaling p r 5 2 s hr (by decide) (scalarRecurrence14 p s hp hs hw he)
  have he1 : 2*(r-1)+1=2*r-1 := by omega
  have he2 : 2*(r-1)=2*r-2 := by omega
  rwa [he1, he2] at ht

#print axioms scalarRecurrence14
#print axioms assertion14
end
end FiniteMT
```

### `Assertion13.lean`

```lean
import CarryTotals
import PowerVanishing
namespace FiniteMT
noncomputable section
open scoped BigOperators

theorem scalarRecurrence13 (p : ℕ) (s : Fin 4 → ℕ) (hp : p.Prime)
    (hs : ∀ i, 0 < s i) (hw : weight s+1 < p) (he : Even (weight s)) :
    ScalarCarryRecurrence p 4 1 s := by
  have hdp : 5 < p := lt_of_le_of_lt (Nat.add_le_add_right (depth_le_weight s hs) 1) hw
  have hlevel : ∀ r, 1 ≤ r → ∀ a, 1 ≤ a → a < 4 →
      carrySum p (r+1) (r+1) s a=(p:ZMod (p^(r+1)))*carrySum p r (r+1) s a := by
    intro r hr a ha had
    let A := ZMod (p^(r+1))
    let T : Fin 3 → A := fun b => carrySum p r (r+1) s (b.val+1)
    let P := parityProjection (2:A)⁻¹ 1 T
    let Q := parityProjection (2:A)⁻¹ (-1) T
    let b : Fin 3 := ⟨a-1,by omega⟩
    have hb : b.val+1=a := by dsimp [b]; omega
    have hTb : T b=carrySum p r (r+1) s a := by simp only [T, hb]
    have hP : P b=carryProject p r (r+1) s 1 a := by
      simp only [P, parityProjection, carryProject, T, (carry_rev_index (d:=4)), hb]
    have hd : P+Q=T := parityProjection_complement (2:A)⁻¹ 1
      (half_mul_two p (r+1) hp (by omega)) T
    have hd' := congrFun hd b
    simp only [Pi.add_apply] at hd'
    have haT : carryAction p 4 (r+1) T a=
        carryAction p 4 (r+1) P a+carryAction p 4 (r+1) Q a := by
      conv_lhs => rw [← hd]
      simp only [carryAction, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    have hm1 := mode4plus p (r+1) hp (by omega) T b
    have hm2 := mode4minus p (r+1) hp (by omega) T b
    rw [hb] at hm1 hm2
    have hz1 := power_mul_zero p (r+1) 1 (2*r-1)
      (carrySum p r (r+1) s a-carryProject p r (r+1) s 1 a)
      (by simpa only [he.neg_one_pow] using
        wrongParity_project_dvd p r (r+1) 4 a s hp hr hdp ha had) (by omega)
    have hzS := power_mul_zero p (r+1) 1 r (carryTotal p r (r+1) s)
      (totalBound4 p s hp hs hw r hr (r+1)) (by omega)
    change (p:A)^1*(∑ b,T b)=0 at hzS
    rw [pow_one] at hzS
    rw [← hP, ← hTb] at hz1
    change (p:A)^1*(T b-P b)=0 at hz1
    rw [pow_one] at hz1
    rw [carrySum_weak_plus p r 4 a s hp hr (by decide) hdp ha]
    change carryAction p 4 (r+1) T a=(p:A)*carrySum p r (r+1) s a
    rw [haT, hm1, hm2, ← hTb]
    change (p:A)*P b+(6:A)⁻¹*((p:A)^3-p)*(∑ b,T b)*(![1,4,1] b)+(p:A)^2*Q b=(p:A)*T b
    linear_combination ((p:A)-1)*hz1+(p:A)^2*hd'+
      (6:A)⁻¹*((p:A)^2-1)*(![1,4,1] b)*hzS
  apply scalarRecurrence_of_exact p 4 1 s hp
  intro r hr a ha had
  have haux (q : ℕ) (hq : q=r+1) : carrySum p (r+1) q s a=
      (p:ZMod (p^q))^1*carrySum p r q s a := by
    subst q
    simpa only [pow_one] using hlevel r hr a ha had
  exact haux (1*r+1) (by omega)

theorem assertion13 : Scaling13 := by
  intro p r s hp hr hs hw he
  have ht := scalar_scaling p r 4 1 s hr (by decide) (scalarRecurrence13 p s hp hs hw he)
  rwa [one_mul, Nat.sub_add_cancel hr] at ht

#print axioms scalarRecurrence13
#print axioms assertion13
end
end FiniteMT
```

### `FinalEndpoint.lean`

```lean
import Assertion12
import Assertion13
import Assertion14
import StrongDivisibility
namespace FiniteMT

/-- Wang and Zhao, Conjecture 3.4, with the unchanged source definitions,
all five assertions, and all original prime, weight, depth and level ranges. -/
theorem wang_zhao_conjecture_3_4 : SourceConjecture :=
  source_of_four assertion12 assertion13 assertion14 assertion15

#print wang_zhao_conjecture_3_4
#print axioms wang_zhao_conjecture_3_4
end FiniteMT
```

### `PrintedExample.lean`

```lean
import Assertion12
namespace FiniteMT
open scoped BigOperators

/-- The congruence in the printed example follows without enumerating tuples.
The separate noncongruence at precision 6 is not asserted here. -/
theorem printed_example13 :
    sumMod 13 3 5 ![8,1,1,1] =
      (13:ZMod (13^5))^4*sumMod 13 1 5 ![8,1,1,1] := by
  exact assertion12 13 3 ![8,1,1,1] (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- An admissible source instance has an explicitly inhabited summation filter. -/
theorem admissible_nonempty13 :
    Nat.Prime 13 ∧ (∀ i : Fin 4, 0 < (![8,1,1,1] i : ℕ)) ∧
      weight ![8,1,1,1]+1 < 13 ∧
      ∃ x : Fin 4 → Fin 13,
        (∀ i, 0 < (x i).val ∧ ¬ 13 ∣ (x i).val) ∧ (∑ i, (x i).val)=13 := by
  refine ⟨by decide, by decide, by decide, ![1,1,1,10], by decide, by decide⟩

#print axioms admissible_nonempty13
#print axioms printed_example13
end FiniteMT
```

### `Stage3Inventory.lean`

```lean
import Endpoint
import Carry
import FourSum
import Sanity
import Taylor
import TaylorSum
import ModularTaylor
import TaylorMoments
import UniformLift
import WeakInduction
import Obligations
import Inventory
import DigitReindex
import CountPolynomial
import InverseCongruence
import CarryReindex
import WeakLift
import Assertion16
import MomentPolynomial
import MomentGap
import ConcreteMoments
import CarryReflection
import CarryFiber
import DoubleLift
import Reduction
import LowReflection
import ReductionKernel
import ReflectionTaylor
import ReductionDouble
import ParityBound
import ShiftedParity
import CountGenerating
import CountRecurrence
import RowKernel
import RowSymmetry
import ProjectedCount
import ScalarScaling
import ProjectionAlgebra
import Remaining
import ProjectedMoment
import Stage2Inventory
import MatrixProjection
import MatrixDivisibility
import ProjectedDerivative
import ProjectedLift
import StrongDivisibility
import FieldCancellation
import InitialCarry
import CarryFormula
import CarryFormulaCoeff
import SmallChoose
import CarryFormulaRange
import Count4Row1
import Count4Row2
import Count4Row3
import Count5Row1
import Count5Row2
import Count5Row3
import Count5Row4
import Count4Table
import Count5Table
import ModeAlgebra4
import ModeAlgebra5
import TotalInduction
import Modes4
import Assertion12
import Modes5
import CarryTotals
import PowerVanishing
import Assertion14
import Assertion13
import FinalEndpoint
import PrintedExample
#check FiniteMT.sumMod_eq_first
#print axioms FiniteMT.sumMod_eq_first
#check FiniteMT.firstMoment_total
#print axioms FiniteMT.firstMoment_total
#check FiniteMT.digitCondition_perm
#print axioms FiniteMT.digitCondition_perm
#check FiniteMT.firstMoment_symm
#print axioms FiniteMT.firstMoment_symm
#check FiniteMT.firstMoment_identity
#print axioms FiniteMT.firstMoment_identity
#check FiniteMT.firstMoment_dvd_of_count
#print axioms FiniteMT.firstMoment_dvd_of_count
#check FiniteMT.fourEquiv_symm_apply
#print axioms FiniteMT.fourEquiv_symm_apply
#check FiniteMT.sum_four
#print axioms FiniteMT.sum_four
#check FiniteMT.sumMod_depth_one
#print axioms FiniteMT.sumMod_depth_one
#check FiniteMT.sanity_weight13
#print axioms FiniteMT.sanity_weight13
#check FiniteMT.sanity_nonempty
#print axioms FiniteMT.sanity_nonempty
#check FiniteMT.sanity_scaling
#print axioms FiniteMT.sanity_scaling
#check FiniteMT.Taylor.jet_mul
#print axioms FiniteMT.Taylor.jet_mul
#check FiniteMT.Taylor.perturb_val
#print axioms FiniteMT.Taylor.perturb_val
#check FiniteMT.Taylor.inverse_perturb
#print axioms FiniteMT.Taylor.inverse_perturb
#check FiniteMT.Taylor.inverse_pow_perturb
#print axioms FiniteMT.Taylor.inverse_pow_perturb
#check FiniteMT.Taylor.product_jets
#print axioms FiniteMT.Taylor.product_jets
#check FiniteMT.Taylor.product_inverse_perturb
#print axioms FiniteMT.Taylor.product_inverse_perturb
#check FiniteMT.Taylor.scaled_cross_zero
#print axioms FiniteMT.Taylor.scaled_cross_zero
#check FiniteMT.Taylor.scaled_quadratic_zero
#print axioms FiniteMT.Taylor.scaled_quadratic_zero
#check FiniteMT.Taylor.sum_product_jets
#print axioms FiniteMT.Taylor.sum_product_jets
#check FiniteMT.Taylor.family_evaluate
#print axioms FiniteMT.Taylor.family_evaluate
#check FiniteMT.Taylor.sum_product_inverse_perturb
#print axioms FiniteMT.Taylor.sum_product_inverse_perturb
#check FiniteMT.Taylor.power_cube_zero
#print axioms FiniteMT.Taylor.power_cube_zero
#check FiniteMT.Taylor.quadratic_moment_zero
#print axioms FiniteMT.Taylor.quadratic_moment_zero
#check FiniteMT.Taylor.inverse_pow_lift
#print axioms FiniteMT.Taylor.inverse_pow_lift
#check FiniteMT.Taylor.coordinate_isUnit
#print axioms FiniteMT.Taylor.coordinate_isUnit
#check FiniteMT.Taylor.finite_product_inverse_lift
#print axioms FiniteMT.Taylor.finite_product_inverse_lift
#check FiniteMT.Taylor.familyCoeff_first
#print axioms FiniteMT.Taylor.familyCoeff_first
#check FiniteMT.Taylor.familyCoeff_second
#print axioms FiniteMT.Taylor.familyCoeff_second
#check FiniteMT.Taylor.scaled_const_moment_zero
#print axioms FiniteMT.Taylor.scaled_const_moment_zero
#check FiniteMT.Taylor.scaled_mixed_moment_zero
#print axioms FiniteMT.Taylor.scaled_mixed_moment_zero
#check FiniteMT.Taylor.sum_inverse_of_digit_moments
#print axioms FiniteMT.Taylor.sum_inverse_of_digit_moments
#check FiniteMT.Taylor.modular_lifted_sum
#print axioms FiniteMT.Taylor.modular_lifted_sum
#check FiniteMT.weak_divisibility_of_carry
#print axioms FiniteMT.weak_divisibility_of_carry
#check FiniteMT.assertion16_of_carry
#print axioms FiniteMT.assertion16_of_carry
#check FiniteMT.depth_le_weight
#print axioms FiniteMT.depth_le_weight
#check FiniteMT.source_of_obligations
#print axioms FiniteMT.source_of_obligations
#check FiniteMT.joinDigits_sum
#print axioms FiniteMT.joinDigits_sum
#check FiniteMT.joinDigits_good
#print axioms FiniteMT.joinDigits_good
#check FiniteMT.low_carry_exists
#print axioms FiniteMT.low_carry_exists
#check FiniteMT.lift_filter
#print axioms FiniteMT.lift_filter
#check FiniteMT.digitPoly_eq
#print axioms FiniteMT.digitPoly_eq
#check FiniteMT.digitPoly_power
#print axioms FiniteMT.digitPoly_power
#check FiniteMT.count_as_coeff
#print axioms FiniteMT.count_as_coeff
#check FiniteMT.expand_gap
#print axioms FiniteMT.expand_gap
#check FiniteMT.carryCount_dvd
#print axioms FiniteMT.carryCount_dvd
#check FiniteMT.unit_inverse_sub
#print axioms FiniteMT.unit_inverse_sub
#check FiniteMT.product_sub_dvd
#print axioms FiniteMT.product_sub_dvd
#check FiniteMT.inverse_product_lift_dvd
#print axioms FiniteMT.inverse_product_lift_dvd
#check FiniteMT.sum_lift_reindex
#print axioms FiniteMT.sum_lift_reindex
#check FiniteMT.carrySum_reindex
#print axioms FiniteMT.carrySum_reindex
#check FiniteMT.digit_constant_sum
#print axioms FiniteMT.digit_constant_sum
#check FiniteMT.base_lift_sum
#print axioms FiniteMT.base_lift_sum
#check FiniteMT.weakCarryRecurrence
#print axioms FiniteMT.weakCarryRecurrence
#check FiniteMT.countTheorem
#print axioms FiniteMT.countTheorem
#check FiniteMT.weakLiftTheorem
#print axioms FiniteMT.weakLiftTheorem
#check FiniteMT.assertion16
#print axioms FiniteMT.assertion16
#check FiniteMT.source_of_four
#print axioms FiniteMT.source_of_four
#check FiniteMT.firstMoment_dvd
#print axioms FiniteMT.firstMoment_dvd
#check FiniteMT.weighted_product
#print axioms FiniteMT.weighted_product
#check FiniteMT.prod_one_factor
#print axioms FiniteMT.prod_one_factor
#check FiniteMT.prod_two_factor
#print axioms FiniteMT.prod_two_factor
#check FiniteMT.one_moment_poly
#print axioms FiniteMT.one_moment_poly
#check FiniteMT.mixed_moment_poly
#print axioms FiniteMT.mixed_moment_poly
#check FiniteMT.weightedDigitPoly_one
#print axioms FiniteMT.weightedDigitPoly_one
#check FiniteMT.weightedDigitPoly_two
#print axioms FiniteMT.weightedDigitPoly_two
#check FiniteMT.moment_gap
#print axioms FiniteMT.moment_gap
#check FiniteMT.digitPoly_derivative
#print axioms FiniteMT.digitPoly_derivative
#check FiniteMT.digitPoly_derivative_two
#print axioms FiniteMT.digitPoly_derivative_two
#check FiniteMT.fiber_weight_coeff
#print axioms FiniteMT.fiber_weight_coeff
#check FiniteMT.mixed_secondMoment_dvd
#print axioms FiniteMT.mixed_secondMoment_dvd
#check FiniteMT.square_secondMoment_dvd
#print axioms FiniteMT.square_secondMoment_dvd
#check FiniteMT.secondMoment_dvd
#print axioms FiniteMT.secondMoment_dvd
#check FiniteMT.reflectDigits_total
#print axioms FiniteMT.reflectDigits_total
#check FiniteMT.digitCondition_reflect
#print axioms FiniteMT.digitCondition_reflect
#check FiniteMT.carryCount_reflection
#print axioms FiniteMT.carryCount_reflection
#check FiniteMT.digitFiber_sum
#print axioms FiniteMT.digitFiber_sum
#check FiniteMT.digitFiber_card
#print axioms FiniteMT.digitFiber_card
#check FiniteMT.digitFiber_first
#print axioms FiniteMT.digitFiber_first
#check FiniteMT.digitFiber_second
#print axioms FiniteMT.digitFiber_second
#check FiniteMT.linear_eq_sum
#print axioms FiniteMT.linear_eq_sum
#check FiniteMT.concrete_lifted_fiber
#print axioms FiniteMT.concrete_lifted_fiber
#check FiniteMT.shifted_product
#print axioms FiniteMT.shifted_product
#check FiniteMT.product_derivative_sum
#print axioms FiniteMT.product_derivative_sum
#check FiniteMT.carrySum_double
#print axioms FiniteMT.carrySum_double
#check FiniteMT.map_zmod_unit_inverse
#print axioms FiniteMT.map_zmod_unit_inverse
#check FiniteMT.reduce_carrySum
#print axioms FiniteMT.reduce_carrySum
#check FiniteMT.reduce_sumMod
#print axioms FiniteMT.reduce_sumMod
#check FiniteMT.reflectLow_val
#print axioms FiniteMT.reflectLow_val
#check FiniteMT.reflectLow_good
#print axioms FiniteMT.reflectLow_good
#check FiniteMT.reflectLow_total
#print axioms FiniteMT.reflectLow_total
#check FiniteMT.lowCondition_reflect
#print axioms FiniteMT.lowCondition_reflect
#check FiniteMT.carrySum_reflection_reindex
#print axioms FiniteMT.carrySum_reflection_reindex
#check FiniteMT.reduction_zero_iff
#print axioms FiniteMT.reduction_zero_iff
#check FiniteMT.reflection_product
#print axioms FiniteMT.reflection_product
#check FiniteMT.carrySum_reflection
#print axioms FiniteMT.carrySum_reflection
#check FiniteMT.reduce_derivativeCarrySum
#print axioms FiniteMT.reduce_derivativeCarrySum
#check FiniteMT.carrySum_double_at
#print axioms FiniteMT.carrySum_double_at
#check FiniteMT.derivativeCarrySum_dvd
#print axioms FiniteMT.derivativeCarrySum_dvd
#check FiniteMT.carrySum_weak_plus
#print axioms FiniteMT.carrySum_weak_plus
#check FiniteMT.sign_square
#print axioms FiniteMT.sign_square
#check FiniteMT.carrySum_reflection_at
#print axioms FiniteMT.carrySum_reflection_at
#check FiniteMT.carrySum_parity_at
#print axioms FiniteMT.carrySum_parity_at
#check FiniteMT.carrySum_parity_difference
#print axioms FiniteMT.carrySum_parity_difference
#check FiniteMT.wrongParity_dvd
#print axioms FiniteMT.wrongParity_dvd
#check FiniteMT.wrongParity_project_dvd
#print axioms FiniteMT.wrongParity_project_dvd
#check FiniteMT.weight_shift
#print axioms FiniteMT.weight_shift
#check FiniteMT.shiftedParity_dvd
#print axioms FiniteMT.shiftedParity_dvd
#check FiniteMT.shiftedParity_project_dvd
#print axioms FiniteMT.shiftedParity_project_dvd
#check FiniteMT.digitPolynomial_power
#print axioms FiniteMT.digitPolynomial_power
#check FiniteMT.count_coefficient
#print axioms FiniteMT.count_coefficient
#check FiniteMT.digitPolynomial_geom
#print axioms FiniteMT.digitPolynomial_geom
#check FiniteMT.digitPolynomial_derivative_relation
#print axioms FiniteMT.digitPolynomial_derivative_relation
#check FiniteMT.countPolynomial_differential
#print axioms FiniteMT.countPolynomial_differential
#check FiniteMT.countPolynomial_coeff_recurrence
#print axioms FiniteMT.countPolynomial_coeff_recurrence
#check FiniteMT.p_cast_multiple_zero
#print axioms FiniteMT.p_cast_multiple_zero
#check FiniteMT.carryCount_row_recurrence
#print axioms FiniteMT.carryCount_row_recurrence
#check FiniteMT.row_normalized
#print axioms FiniteMT.row_normalized
#check FiniteMT.row_reversal
#print axioms FiniteMT.row_reversal
#check FiniteMT.choose_isUnit_mod_prime_square
#print axioms FiniteMT.choose_isUnit_mod_prime_square
#check FiniteMT.carryCount_column_parity
#print axioms FiniteMT.carryCount_column_parity
#check FiniteMT.sum_reflection_cancel
#print axioms FiniteMT.sum_reflection_cancel
#check FiniteMT.carryCount_column_parity_at
#print axioms FiniteMT.carryCount_column_parity_at
#check FiniteMT.projected_count_zero
#print axioms FiniteMT.projected_count_zero
#check FiniteMT.projected_count_dvd
#print axioms FiniteMT.projected_count_dvd
#check FiniteMT.scalar_scaling_dvd
#print axioms FiniteMT.scalar_scaling_dvd
#check FiniteMT.scalar_scaling
#print axioms FiniteMT.scalar_scaling
#check FiniteMT.parityProjection_add
#print axioms FiniteMT.parityProjection_add
#check FiniteMT.parityProjection_smul
#print axioms FiniteMT.parityProjection_smul
#check FiniteMT.parityProjection_complement
#print axioms FiniteMT.parityProjection_complement
#check FiniteMT.parityProjection_idempotent
#print axioms FiniteMT.parityProjection_idempotent
#check FiniteMT.parityProjection_opposite
#print axioms FiniteMT.parityProjection_opposite
#check FiniteMT.carryAction_projection
#print axioms FiniteMT.carryAction_projection
#check FiniteMT.firstMoment_cast_identity
#print axioms FiniteMT.firstMoment_cast_identity
#check FiniteMT.source_of_recurrences
#print axioms FiniteMT.source_of_recurrences
#check FiniteMT.carryCount_pair_dvd
#print axioms FiniteMT.carryCount_pair_dvd
#check FiniteMT.firstMoment_cross_dvd
#print axioms FiniteMT.firstMoment_cross_dvd
#check FiniteMT.matrixAction_add
#print axioms FiniteMT.matrixAction_add
#check FiniteMT.projected_matrix_action
#print axioms FiniteMT.projected_matrix_action
#check FiniteMT.projected_matrix_cross
#print axioms FiniteMT.projected_matrix_cross
#check FiniteMT.matrixAction_dvd
#print axioms FiniteMT.matrixAction_dvd
#check FiniteMT.projected_matrix_cross_dvd
#print axioms FiniteMT.projected_matrix_cross_dvd
#check FiniteMT.projected_matrix_dvd
#print axioms FiniteMT.projected_matrix_dvd
#check FiniteMT.half_mul_two
#print axioms FiniteMT.half_mul_two
#check FiniteMT.carry_rev_index
#print axioms FiniteMT.carry_rev_index
#check FiniteMT.projected_derivative_dvd
#print axioms FiniteMT.projected_derivative_dvd
#check FiniteMT.odd_total_sign
#print axioms FiniteMT.odd_total_sign
#check FiniteMT.projectedCarryLift
#print axioms FiniteMT.projectedCarryLift
#check FiniteMT.carryAction_project_power_dvd
#print axioms FiniteMT.carryAction_project_power_dvd
#check FiniteMT.carrySum_dvd_of_zero
#print axioms FiniteMT.carrySum_dvd_of_zero
#check FiniteMT.strongCarryDivisibility
#print axioms FiniteMT.strongCarryDivisibility
#check FiniteMT.assertion15
#print axioms FiniteMT.assertion15
#check FiniteMT.residueCarrySum_scaling
#print axioms FiniteMT.residueCarrySum_scaling
#check FiniteMT.residueCarrySum_zero
#print axioms FiniteMT.residueCarrySum_zero
#check FiniteMT.carry_indicator_sum
#print axioms FiniteMT.carry_indicator_sum
#check FiniteMT.initial_total_reindex
#print axioms FiniteMT.initial_total_reindex
#check FiniteMT.initialCarryCancellation
#print axioms FiniteMT.initialCarryCancellation
#check FiniteMT.count_series
#print axioms FiniteMT.count_series
#check FiniteMT.count_formula_cutoff
#print axioms FiniteMT.count_formula_cutoff
#check FiniteMT.choose_three_shift
#print axioms FiniteMT.choose_three_shift
#check FiniteMT.choose_four_shift
#print axioms FiniteMT.choose_four_shift
#check FiniteMT.count_formula
#print axioms FiniteMT.count_formula
#check FiniteMT.scaled_count_4_1_1
#print axioms FiniteMT.scaled_count_4_1_1
#check FiniteMT.scaled_count_4_1_2
#print axioms FiniteMT.scaled_count_4_1_2
#check FiniteMT.scaled_count_4_1_3
#print axioms FiniteMT.scaled_count_4_1_3
#check FiniteMT.scaled_count_4_2_1
#print axioms FiniteMT.scaled_count_4_2_1
#check FiniteMT.scaled_count_4_2_2
#print axioms FiniteMT.scaled_count_4_2_2
#check FiniteMT.scaled_count_4_2_3
#print axioms FiniteMT.scaled_count_4_2_3
#check FiniteMT.scaled_count_4_3_1
#print axioms FiniteMT.scaled_count_4_3_1
#check FiniteMT.scaled_count_4_3_2
#print axioms FiniteMT.scaled_count_4_3_2
#check FiniteMT.scaled_count_4_3_3
#print axioms FiniteMT.scaled_count_4_3_3
#check FiniteMT.scaled_count_5_1_1
#print axioms FiniteMT.scaled_count_5_1_1
#check FiniteMT.scaled_count_5_1_2
#print axioms FiniteMT.scaled_count_5_1_2
#check FiniteMT.scaled_count_5_1_3
#print axioms FiniteMT.scaled_count_5_1_3
#check FiniteMT.scaled_count_5_1_4
#print axioms FiniteMT.scaled_count_5_1_4
#check FiniteMT.scaled_count_5_2_1
#print axioms FiniteMT.scaled_count_5_2_1
#check FiniteMT.scaled_count_5_2_2
#print axioms FiniteMT.scaled_count_5_2_2
#check FiniteMT.scaled_count_5_2_3
#print axioms FiniteMT.scaled_count_5_2_3
#check FiniteMT.scaled_count_5_2_4
#print axioms FiniteMT.scaled_count_5_2_4
#check FiniteMT.scaled_count_5_3_1
#print axioms FiniteMT.scaled_count_5_3_1
#check FiniteMT.scaled_count_5_3_2
#print axioms FiniteMT.scaled_count_5_3_2
#check FiniteMT.scaled_count_5_3_3
#print axioms FiniteMT.scaled_count_5_3_3
#check FiniteMT.scaled_count_5_3_4
#print axioms FiniteMT.scaled_count_5_3_4
#check FiniteMT.scaled_count_5_4_1
#print axioms FiniteMT.scaled_count_5_4_1
#check FiniteMT.scaled_count_5_4_2
#print axioms FiniteMT.scaled_count_5_4_2
#check FiniteMT.scaled_count_5_4_3
#print axioms FiniteMT.scaled_count_5_4_3
#check FiniteMT.scaled_count_5_4_4
#print axioms FiniteMT.scaled_count_5_4_4
#check FiniteMT.scaled_count4
#print axioms FiniteMT.scaled_count4
#check FiniteMT.scaled_count5
#print axioms FiniteMT.scaled_count5
#check FiniteMT.matrix4minus
#print axioms FiniteMT.matrix4minus
#check FiniteMT.matrix4plus
#print axioms FiniteMT.matrix4plus
#check FiniteMT.matrix5plus
#print axioms FiniteMT.matrix5plus
#check FiniteMT.reduce_carryTotal
#print axioms FiniteMT.reduce_carryTotal
#check FiniteMT.carryTotal_dvd_of_zero
#print axioms FiniteMT.carryTotal_dvd_of_zero
#check FiniteMT.carryTotal_induction
#print axioms FiniteMT.carryTotal_induction
#check FiniteMT.scalarRecurrence_of_exact
#print axioms FiniteMT.scalarRecurrence_of_exact
#check FiniteMT.small_unit
#print axioms FiniteMT.small_unit
#check FiniteMT.six_unit
#print axioms FiniteMT.six_unit
#check FiniteMT.scaled_carryAction4
#print axioms FiniteMT.scaled_carryAction4
#check FiniteMT.mode4minus
#print axioms FiniteMT.mode4minus
#check FiniteMT.mode4plus
#print axioms FiniteMT.mode4plus
#check FiniteMT.scalarRecurrence12
#print axioms FiniteMT.scalarRecurrence12
#check FiniteMT.assertion12
#print axioms FiniteMT.assertion12
#check FiniteMT.twentyfour_unit
#print axioms FiniteMT.twentyfour_unit
#check FiniteMT.scaled_carryAction5
#print axioms FiniteMT.scaled_carryAction5
#check FiniteMT.mode5plus
#print axioms FiniteMT.mode5plus
#check FiniteMT.sum_projection_plus
#print axioms FiniteMT.sum_projection_plus
#check FiniteMT.carryAction_total4
#print axioms FiniteMT.carryAction_total4
#check FiniteMT.carryAction_total5
#print axioms FiniteMT.carryAction_total5
#check FiniteMT.totalBound4
#print axioms FiniteMT.totalBound4
#check FiniteMT.totalBound5
#print axioms FiniteMT.totalBound5
#check FiniteMT.power_mul_zero
#print axioms FiniteMT.power_mul_zero
#check FiniteMT.scalarRecurrence14
#print axioms FiniteMT.scalarRecurrence14
#check FiniteMT.assertion14
#print axioms FiniteMT.assertion14
#check FiniteMT.scalarRecurrence13
#print axioms FiniteMT.scalarRecurrence13
#check FiniteMT.assertion13
#print axioms FiniteMT.assertion13
#check FiniteMT.wang_zhao_conjecture_3_4
#print axioms FiniteMT.wang_zhao_conjecture_3_4
#check FiniteMT.printed_example13
#print axioms FiniteMT.printed_example13
#check FiniteMT.admissible_nonempty13
#print axioms FiniteMT.admissible_nonempty13
#print FiniteMT.SourceConjecture
#print FiniteMT.Conclusions
#print FiniteMT.ProjectedCarryLift
#print FiniteMT.StrongCarryDivisibility
#print FiniteMT.InitialCarryCancellation
#print FiniteMT.Scaling12
#print FiniteMT.Scaling13
#print FiniteMT.Scaling14
#print FiniteMT.Divisibility15
#print FiniteMT.wang_zhao_conjecture_3_4
```
