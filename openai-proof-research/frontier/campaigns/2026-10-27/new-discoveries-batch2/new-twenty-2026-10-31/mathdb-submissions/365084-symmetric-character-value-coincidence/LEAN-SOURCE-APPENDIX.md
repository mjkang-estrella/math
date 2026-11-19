# Exact Lean appendix for MathDB 365084

Fifty-eight canonical author modules.

## CauchyDeterminant.lean

```lean
import Mathlib.LinearAlgebra.Matrix.SchurComplement

open scoped BigOperators
open Matrix

namespace LiteralColoring

private theorem cauchy_residual {R : Type*} [CommRing R]
    (x y a b k p q : R)
    (hk : k * (1-x*y) = 1) (hp : p * (1-x*b) = 1) (hq : q * (1-a*y) = 1) :
    k - p * (1-a*b) * q = ((x-a)*p) * (((y-b)*q)*k) := by
  calc
    _ = k * ((p * (1-x*b)) * (q * (1-a*y))) -
        (p * (1-a*b) * q) * (k * (1-x*y)) := by rw [hp, hq, hk]; ring
    _ = _ := by ring

def vandermondeFactors {R : Type*} [CommRing R] : {n : ℕ} → (Fin n → R) → R
  | 0, _ => 1
  | n + 1, x => (∏ i : Fin n, (x i.succ - x 0)) * vandermondeFactors (fun i => x i.succ)

theorem det_cauchy_of_inverse {R : Type*} [CommRing R] {n : ℕ}
    (x y : Fin n → R) (K : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, K i j * (1 - x i * y j) = 1) :
    K.det = vandermondeFactors x * vandermondeFactors y * (∏ i, ∏ j, K i j) := by
  classical
  induction n with
  | zero => simp [vandermondeFactors]
  | succ n ih =>
    let A : Matrix (Fin 1) (Fin 1) R := of fun _ _ => K 0 0
    let B : Matrix (Fin 1) (Fin n) R := of fun _ j => K 0 j.succ
    let C : Matrix (Fin n) (Fin 1) R := of fun i _ => K i.succ 0
    let D : Matrix (Fin n) (Fin n) R := of fun i j => K i.succ j.succ
    let Z : Matrix (Fin 1) (Fin 1) R := of fun _ _ => 1 - x 0 * y 0
    let _ : Invertible A := ⟨Z,
      by ext i j; fin_cases i; fin_cases j; simpa [A, Z, Matrix.mul_apply, Fin.sum_univ_one, mul_comm] using h 0 0,
      by ext i j; fin_cases i; fin_cases j; simpa [A, Z, Matrix.mul_apply, Fin.sum_univ_one] using h 0 0⟩
    let e : Fin 1 ⊕ Fin n ≃ Fin (n + 1) := finSumFinEquiv.trans (finCongr (Nat.add_comm 1 n))
    have einl (i : Fin 1) : e (Sum.inl i) = 0 := by
      fin_cases i
      rfl
    have einr (i : Fin n) : e (Sum.inr i) = i.succ := by
      apply Fin.ext
      change 1 + i.val = i.val + 1
      omega
    have he : Matrix.reindex e.symm e.symm K = fromBlocks A B C D := by
      ext i j
      cases i <;> cases j <;> simp [Matrix.reindex_apply, einl, einr, A, B, C, D]
    have hs : D - C * ⅟A * B =
        of (fun i j => ((x i.succ - x 0) * K i.succ 0) *
          (((y j.succ - y 0) * K 0 j.succ) * D i j)) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_one, Matrix.of_apply, D, C, B]
      change K i.succ j.succ - K i.succ 0 * (1-x 0*y 0) * K 0 j.succ = _
      exact cauchy_residual _ _ _ _ _ _ _ (h i.succ j.succ) (h i.succ 0) (h 0 j.succ)
    have hD := ih (fun i => x i.succ) (fun j => y j.succ) D (fun i j => h i.succ j.succ)
    have hA : A.det = K 0 0 := by simp [A]
    have hp : (∏ i, ∏ j, K i j) = (K 0 0 * ∏ j : Fin n, K 0 j.succ) *
        ((∏ i : Fin n, K i.succ 0) * ∏ i : Fin n, ∏ j : Fin n, K i.succ j.succ) := by
      rw [Fin.prod_univ_succ]
      simp_rw [Fin.prod_univ_succ (fun j : Fin (n + 1) => K _ j)]
      rw [Finset.prod_mul_distrib]
    rw [← det_reindex_self e.symm K, he, det_fromBlocks₁₁, hs]
    have hdet :
        (of (fun i j => ((x i.succ - x 0) * K i.succ 0) *
          (((y j.succ - y 0) * K 0 j.succ) * D i j))).det =
        (∏ i : Fin n, (x i.succ - x 0) * K i.succ 0) *
          ((∏ j : Fin n, (y j.succ - y 0) * K 0 j.succ) * D.det) := by
      calc
        _ = (∏ i : Fin n, (x i.succ - x 0) * K i.succ 0) *
            (of (fun i j => ((y j.succ - y 0) * K 0 j.succ) * D i j)).det :=
          det_mul_column _ (of fun i j => ((y j.succ - y 0) * K 0 j.succ) * D i j)
        _ = _ := congrArg (_ * ·) (det_mul_row _ D)
    rw [hdet, hA, hD, hp]
    simp only [vandermondeFactors, Finset.prod_mul_distrib, D, Matrix.of_apply]
    ring

end LiteralColoring

#print axioms LiteralColoring.det_cauchy_of_inverse
```

## FixedColor.lean

```lean
import Mathlib.RepresentationTheory.Character
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Fintype.EquivFin

open scoped BigOperators
open Lean

#eval Lean.versionString

namespace LiteralColoring

noncomputable section

def margin {n ell : ℕ} (f : Fin n → Fin ell) (i : Fin ell) : ℕ :=
  Nat.card {x // f x = i}

abbrev Coloring {n ell : ℕ} (a : Fin ell → ℕ) :=
  {f : Fin n → Fin ell // ∀ i, margin f i = a i}

theorem margin_precomp {n ell : ℕ} (f : Fin n → Fin ell) (e : Equiv.Perm (Fin n))
    (i : Fin ell) : margin (f ∘ e) i = margin f i :=
  Nat.card_congr (e.subtypeEquiv fun _ => Iff.rfl)

instance {n ell : ℕ} (a : Fin ell → ℕ) : MulAction (Equiv.Perm (Fin n)) (Coloring (n := n) a) where
  smul g f := ⟨f.val ∘ (g⁻¹ : Equiv.Perm (Fin n)), fun i => (margin_precomp f.val g⁻¹ i).trans (f.property i)⟩
  one_smul f := Subtype.ext rfl
  mul_smul g h f := Subtype.ext (by
    funext x
    change f.val ((g * h)⁻¹ x) = f.val (h⁻¹ (g⁻¹ x))
    rw [mul_inv_rev]
    rfl)

theorem smul_apply {n ell : ℕ} {a : Fin ell → ℕ} (g : Equiv.Perm (Fin n))
    (f : Coloring (n := n) a) (x : Fin n) : (g • f).val x = f.val (g⁻¹ x) := rfl

def coloringRep {n ell : ℕ} (a : Fin ell → ℕ) : FDRep ℂ (Equiv.Perm (Fin n)) :=
  FDRep.of (Representation.ofMulAction ℂ (Equiv.Perm (Fin n)) (Coloring (n := n) a))

abbrev FixedColorings {n ell : ℕ} (g : Equiv.Perm (Fin n)) (a : Fin ell → ℕ) :=
  {f : Coloring (n := n) a // g • f = f}

theorem character_eq_fixed {n ell : ℕ} (a : Fin ell → ℕ) (g : Equiv.Perm (Fin n)) :
    (coloringRep a).character g = (Nat.card (FixedColorings g a) : ℂ) := by
  classical
  let _ : Fintype (Coloring (n := n) a) := Fintype.ofFinite _
  let b := MonoidAlgebra.basis (Coloring (n := n) a) ℂ
  rw [FDRep.character]
  change LinearMap.trace ℂ _ (Representation.ofMulAction ℂ _ (Coloring (n := n) a) g) = _
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  have h (f : Coloring (n := n) a) :
      LinearMap.toMatrix b b (Representation.ofMulAction ℂ _ (Coloring (n := n) a) g) f f =
        if g • f = f then 1 else 0 := by
    rw [LinearMap.toMatrix_apply, show b f = MonoidAlgebra.single f 1 from rfl,
      Representation.ofMulAction_single]
    change Finsupp.single (g • f) (1 : ℂ) f = _
    rw [Finsupp.single_apply]
  simp only [Matrix.diag_apply, h]
  rw [← Finset.sum_filter]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype]

end

end LiteralColoring

#print axioms LiteralColoring.margin_precomp
#print axioms LiteralColoring.smul_apply
#print axioms LiteralColoring.coloringRep
#print axioms LiteralColoring.character_eq_fixed
```

## GeometricCoefficients.lean

```lean
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Basic.Complex.Basic

open scoped BigOperators
open MvPowerSeries

namespace LiteralColoring

noncomputable section

def geometric {S : Type*} (e : S →₀ ℕ) : MvPowerSeries S ℂ := by
  classical
  exact fun d => if ∃ k : ℕ, d = k • e then 1 else 0

theorem coeff_geometric {S : Type*} (e d : S →₀ ℕ) [Decidable (∃ k : ℕ, d = k • e)] :
    coeff d (geometric e) = if ∃ k : ℕ, d = k • e then 1 else 0 := by
  change @ite ℂ (∃ k : ℕ, d = k • e) (Classical.propDecidable _) 1 0 = _
  congr

theorem geometric_mul_sub {S : Type*} (e : S →₀ ℕ) (he : e ≠ 0) :
    geometric e * (1 - monomial e (1 : ℂ)) = 1 := by
  classical
  rw [mul_sub, mul_one, sub_eq_iff_eq_add, mul_comm (geometric e)]
  ext d
  simp only [map_add, coeff_one, coeff_monomial_mul, coeff_geometric, one_mul]
  by_cases hz : d = 0
  · subst d
    have hn : ¬ e ≤ 0 := fun h => he (le_antisymm h bot_le)
    simp [hn, show ∃ k : ℕ, (0 : S →₀ ℕ) = k • e from ⟨0, by simp⟩]
  · have hiff : (∃ k : ℕ, d = k • e) ↔
        e ≤ d ∧ ∃ k : ℕ, d - e = k • e := by
      constructor
      · rintro ⟨k, hk⟩
        cases k with
        | zero => exact (hz (by simpa using hk)).elim
        | succ k =>
          rw [succ_nsmul] at hk
          exact ⟨by rw [hk]; exact le_add_self, ⟨k, by rw [hk, add_tsub_cancel_right]⟩⟩
      · rintro ⟨hle, k, hk⟩
        exact ⟨k + 1, by rw [succ_nsmul, ← hk, tsub_add_cancel_of_le hle]⟩
    simp only [ite_eq_right hz, zero_add]
    by_cases hle : e ≤ d
    · simp [hle, hiff]
    · simp [hle, hiff]

abbrev WeightFiber {I S : Type*} [Fintype I] (E : I → S →₀ ℕ) (d : S →₀ ℕ) :=
  {k : I → ℕ // ∑ i, k i • E i = d}

theorem coeff_prod_geometric {I S : Type*} [Fintype I] (E : I → S →₀ ℕ)
    (hinj : ∀ i, Function.Injective (fun k : ℕ => k • E i)) (d : S →₀ ℕ) :
    coeff d (∏ i, geometric (E i)) = (Nat.card (WeightFiber E d) : ℂ) := by
  classical
  let T := ((Finset.univ : Finset I).finsuppAntidiag d).filter
    (fun l => ∀ i, ∃ k : ℕ, l i = k • E i)
  have hT (l : I →₀ S →₀ ℕ) :
      l ∈ T ↔ (∑ i, l i = d) ∧ ∀ i, ∃ k : ℕ, l i = k • E i := by
    simp [T, Finset.mem_finsuppAntidiag]
  have hprod (l : I →₀ S →₀ ℕ) :
      (∏ i, coeff (l i) (geometric (E i))) =
        if ∀ i, ∃ k : ℕ, l i = k • E i then 1 else 0 := by
    by_cases h : ∀ i, ∃ k : ℕ, l i = k • E i
    · simp [coeff_geometric, h]
    · push Not at h
      obtain ⟨i, hi⟩ := h
      have hz : ¬ ∀ j, ∃ k : ℕ, l j = k • E j := fun h => hi _ (h i).choose_spec
      rw [ite_eq_right hz, Finset.prod_eq_zero (Finset.mem_univ i)]
      simp [coeff_geometric, not_exists.mpr hi]
  rw [coeff_prod]
  simp_rw [hprod, ← Finset.sum_filter, Finset.sum_const, nsmul_one]
  congr 1
  let F (l : T) (i : I) := Classical.choose (((hT l.val).mp l.property).2 i)
  have hF (l : T) (i : I) : l.val i = F l i • E i :=
    Classical.choose_spec (((hT l.val).mp l.property).2 i)
  let e : T ≃ WeightFiber E d :=
    { toFun := fun l => ⟨F l, by simpa only [← hF l] using ((hT l.val).mp l.property).1⟩
      invFun := fun k => ⟨Finsupp.equivFunOnFinite.symm (fun i => k.val i • E i),
        (hT _).mpr ⟨k.property, fun i => ⟨k.val i, rfl⟩⟩⟩
      left_inv := fun l => Subtype.ext (Finsupp.ext fun i => (hF l i).symm)
      right_inv := fun k => Subtype.ext (funext fun i => hinj i (hF _ i).symm) }
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

end

end LiteralColoring

#print axioms LiteralColoring.geometric_mul_sub
#print axioms LiteralColoring.coeff_prod_geometric
```

## CycleColor.lean

```lean
import FixedColor
import Mathlib.GroupTheory.Perm.Cycle.Type

open scoped BigOperators

namespace LiteralColoring

noncomputable section

theorem card_comp_fiber {A B C : Type*} [Finite A] [Finite B]
    (p : A → B) (f : B → C) (i : C) :
    Nat.card {x // f (p x) = i} =
      (let _ := Fintype.ofFinite {b // f b = i}
       ∑ b : {b // f b = i}, Nat.card {x // p x = b.val}) := by
  classical
  let _ := Fintype.ofFinite {b // f b = i}
  change _ = ∑ b : {b // f b = i}, Nat.card {x // p x = b.val}
  let q : {x // f (p x) = i} → {b // f b = i} := fun x => ⟨p x.val, x.property⟩
  let e (b : {b // f b = i}) :
      {x : {x // f (p x) = i} // q x = b} ≃ {x // p x = b.val} :=
    { toFun := fun x => ⟨x.val.val, congrArg Subtype.val x.property⟩
      invFun := fun x =>
        ⟨⟨x.val, by rw [x.property]; exact b.property⟩, Subtype.ext x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv q), Nat.card_sigma]
  exact Finset.sum_congr rfl (fun b _ => Nat.card_congr (e b))

abbrev Cycles {n : ℕ} (g : Equiv.Perm (Fin n)) :=
  Quotient (Equiv.Perm.SameCycle.setoid g)

def cycleOfPoint {n : ℕ} (g : Equiv.Perm (Fin n)) (x : Fin n) : Cycles g :=
  Quotient.mk _ x

def cycleWeight {n : ℕ} (g : Equiv.Perm (Fin n)) (c : Cycles g) : ℕ :=
  Nat.card {x // cycleOfPoint g x = c}

def cycleMargin {n ell : ℕ} {g : Equiv.Perm (Fin n)}
    (c : Cycles g → Fin ell) (i : Fin ell) : ℕ :=
  let _ := Fintype.ofFinite {b // c b = i}
  ∑ b : {b // c b = i}, cycleWeight g b.val

abbrev CycleColorings {n ell : ℕ} (g : Equiv.Perm (Fin n)) (a : Fin ell → ℕ) :=
  {c : Cycles g → Fin ell // ∀ i, cycleMargin c i = a i}

theorem margin_pullback {n ell : ℕ} {g : Equiv.Perm (Fin n)}
    (c : Cycles g → Fin ell) (i : Fin ell) :
    margin (c ∘ cycleOfPoint g) i = cycleMargin c i :=
  card_comp_fiber (cycleOfPoint g) c i

theorem fixed_constant {n ell : ℕ} {g : Equiv.Perm (Fin n)} {a : Fin ell → ℕ}
    (f : FixedColorings g a) {x y : Fin n} (h : g.SameCycle x y) :
    f.val.val x = f.val.val y := by
  let H : Subgroup (Equiv.Perm (Fin n)) :=
    { carrier := {p | ∀ z, f.val.val (p z) = f.val.val z}
      one_mem' := fun _ => rfl
      mul_mem' := fun hp hq z => (hp _).trans (hq z)
      inv_mem' := fun {p} hp z => by
        have hz := hp (p⁻¹ z)
        simpa using hz.symm }
  have hg : g ∈ H := by
    intro z
    have hz := congrArg (fun c : Coloring (n := n) a => c.val (g z)) f.property
    simpa only [smul_apply, show g⁻¹ (g z) = z from g.symm_apply_apply z] using hz.symm
  obtain ⟨j, rfl⟩ := h
  exact (H.zpow_mem hg j x).symm

def fixedEquivCycles {n ell : ℕ} (g : Equiv.Perm (Fin n)) (a : Fin ell → ℕ) :
    FixedColorings g a ≃ CycleColorings g a where
  toFun f :=
    let c : Cycles g → Fin ell := Quotient.lift f.val.val (fun _ _ h => fixed_constant f h)
    ⟨c, fun i => (margin_pullback c i).symm.trans (f.val.property i)⟩
  invFun c :=
    ⟨⟨c.val ∘ cycleOfPoint g, fun i => (margin_pullback c.val i).trans (c.property i)⟩,
      Subtype.ext (funext fun x => congrArg c.val (Quotient.sound (s := Equiv.Perm.SameCycle.setoid g)
        (show g.SameCycle (g⁻¹ x) x from ⟨1, by simp⟩)))⟩
  left_inv _ := rfl
  right_inv c := Subtype.ext (funext fun b => Quotient.inductionOn b (fun _ => rfl))

theorem character_eq_cycleColorings {n ell : ℕ} (g : Equiv.Perm (Fin n)) (a : Fin ell → ℕ) :
    (coloringRep a).character g = (Nat.card (CycleColorings g a) : ℂ) := by
  rw [character_eq_fixed, Nat.card_congr (fixedEquivCycles g a)]

end

end LiteralColoring

#print axioms LiteralColoring.card_comp_fiber
#print axioms LiteralColoring.cycleOfPoint
#print axioms LiteralColoring.cycleWeight
#print axioms LiteralColoring.cycleMargin
#print axioms LiteralColoring.margin_pullback
#print axioms LiteralColoring.fixed_constant
#print axioms LiteralColoring.fixedEquivCycles
#print axioms LiteralColoring.character_eq_cycleColorings
```

## CycleTypeColor.lean

```lean
import CycleColor

open scoped BigOperators
open Equiv.Perm

namespace LiteralColoring

noncomputable section

abbrev CycleIndex {n : ℕ} (g : Equiv.Perm (Fin n)) :=
  {x // g x = x} ⊕ ↥g.cycleFactorsFinset

def indexWeight {n : ℕ} {g : Equiv.Perm (Fin n)} : CycleIndex g → ℕ
  | Sum.inl _ => 1
  | Sum.inr c => c.val.support.card

def fullCycleType {n : ℕ} (g : Equiv.Perm (Fin n)) : Multiset ℕ :=
  g.cycleType + Multiset.replicate (n - g.support.card) 1

def pointIndex {n : ℕ} (g : Equiv.Perm (Fin n)) (x : Fin n) : CycleIndex g :=
  if h : g x = x then Sum.inl ⟨x,h⟩
  else Sum.inr ⟨g.cycleOf x, cycleOf_mem_cycleFactorsFinset_iff.mpr (mem_support.mpr h)⟩

theorem pointIndex_eq_iff {n : ℕ} (g : Equiv.Perm (Fin n)) (x y : Fin n) :
    pointIndex g x = pointIndex g y ↔ g.SameCycle x y := by
  by_cases hx : g x = x
  · constructor
    · intro h
      by_cases hy : g y = y
      · have he : x = y := by simpa [pointIndex, hx, hy] using h
        exact he.sameCycle g
      · simp [pointIndex, hx, hy] at h
    · intro h
      obtain rfl := h.eq_of_left hx
      rfl
  · by_cases hy : g y = y
    · constructor
      · simp [pointIndex, hx, hy]
      · intro h
        exact (hx (h.apply_eq_self_iff.mpr hy)).elim
    · simpa [pointIndex, hx, hy] using
        (sameCycle_iff_cycleOf_eq_of_mem_support (mem_support.mpr hx) (mem_support.mpr hy)).symm

theorem pointIndex_surjective {n : ℕ} (g : Equiv.Perm (Fin n)) :
    Function.Surjective (pointIndex g) := by
  intro c
  cases c with
  | inl x => exact ⟨x.val, by simp [pointIndex, x.property]⟩
  | inr c =>
    obtain ⟨x, hx⟩ := IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp c.property).1
    have heq := (g.eq_cycleOf_of_mem_cycleFactorsFinset_iff c.val c.property x).mpr hx
    have hmem : x ∈ g.support := cycleOf_mem_cycleFactorsFinset_iff.mp (heq ▸ c.property)
    refine ⟨x, ?_⟩
    simp only [pointIndex, dite_eq_right (mem_support.mp hmem), Sum.inr.injEq]
    exact Subtype.ext heq.symm

def cyclesEquivIndex {n : ℕ} (g : Equiv.Perm (Fin n)) : Cycles g ≃ CycleIndex g :=
  Equiv.ofBijective (Quotient.lift (pointIndex g) (fun a b h => (pointIndex_eq_iff g a b).mpr h))
    ⟨by
      intro c d
      induction c using Quotient.inductionOn with
      | _ x =>
        induction d using Quotient.inductionOn with
        | _ y =>
          exact fun h => Quotient.sound ((pointIndex_eq_iff g x y).mp h),
     fun u => by
      obtain ⟨x,hx⟩ := pointIndex_surjective g u
      exact ⟨cycleOfPoint g x, hx⟩⟩

theorem cyclesEquivIndex_apply {n : ℕ} (g : Equiv.Perm (Fin n)) (x : Fin n) :
    cyclesEquivIndex g (cycleOfPoint g x) = pointIndex g x := rfl

theorem cycleWeight_eq_indexWeight {n : ℕ} (g : Equiv.Perm (Fin n)) (c : Cycles g) :
    cycleWeight g c = indexWeight (cyclesEquivIndex g c) := by
  have h (x : Fin n) :
      cycleOfPoint g x = c ↔ pointIndex g x = cyclesEquivIndex g c :=
    (cyclesEquivIndex g).injective.eq_iff.symm
  rw [cycleWeight, Nat.card_congr ((Equiv.refl _).subtypeEquiv (q := fun x => pointIndex g x = cyclesEquivIndex g c) h)]
  generalize cyclesEquivIndex g c = u
  cases u with
  | inl y =>
    have he (x : Fin n) : pointIndex g x = Sum.inl y ↔ x = y.val := by
      rw [← show pointIndex g y.val = Sum.inl y by simp [pointIndex, y.property],
        pointIndex_eq_iff]
      exact ⟨fun hs => hs.eq_of_right y.property, fun h => h.sameCycle g⟩
    rw [Nat.card_congr ((Equiv.refl _).subtypeEquiv (q := fun x => x = y.val) he), indexWeight,
      Nat.card_eq_fintype_card, Fintype.card_subtype_eq]
  | inr p =>
    have he (x : Fin n) : pointIndex g x = Sum.inr p ↔ x ∈ p.val.support := by
      rw [← g.eq_cycleOf_of_mem_cycleFactorsFinset_iff p.val p.property]
      by_cases hx : g x = x
      · constructor
        · simp [pointIndex, hx]
        · intro h
          have hmem := cycleOf_mem_cycleFactorsFinset_iff.mp (h ▸ p.property)
          exact (mem_support.mp hmem hx).elim
      · simp [pointIndex, hx, eq_comm, Subtype.ext_iff]
    rw [Nat.card_congr ((Equiv.refl _).subtypeEquiv (q := fun x => x ∈ p.val.support) he), indexWeight,
      Nat.card_eq_fintype_card, Fintype.card_coe]

def cycleWeights {n : ℕ} (g : Equiv.Perm (Fin n)) : Multiset ℕ :=
  let _ := Fintype.ofFinite (Cycles g)
  Finset.univ.val.map (cycleWeight g)

theorem cycleWeights_eq_fullCycleType {n : ℕ} (g : Equiv.Perm (Fin n)) :
    cycleWeights g = fullCycleType g := by
  classical
  let _ := Fintype.ofFinite (Cycles g)
  change Finset.univ.val.map (cycleWeight g) = _
  simp_rw [cycleWeight_eq_indexWeight]
  rw [← Function.comp_def, ← Multiset.map_map, Multiset.map_univ_val_equiv]
  rw [← Finset.univ_disjSum_univ]
  change (Multiset.map Sum.inl (Finset.univ : Finset {x // g x = x}).val +
    Multiset.map Sum.inr (Finset.univ : Finset ↥g.cycleFactorsFinset).val).map indexWeight = _
  rw [Multiset.map_add, Multiset.map_map, Multiset.map_map]
  change (Finset.univ : Finset {x // g x = x}).val.map (fun _ => 1) +
    (Finset.univ : Finset ↥g.cycleFactorsFinset).val.map ((Finset.card ∘ support) ∘ Subtype.val) = _
  rw [Multiset.map_const', ← Finset.card_def, Finset.card_univ, ← Multiset.map_map,
    Finset.univ_eq_attach, Finset.attach_val, Multiset.attach_map_val, ← cycleType_def]
  have e : {x // g x = x} ≃ ↥g.supportᶜ :=
    (Equiv.refl _).subtypeEquiv fun x => by simp [mem_support]
  rw [Fintype.card_congr e, Fintype.card_coe, Finset.card_compl, Fintype.card_fin,
    fullCycleType, add_comm]

end

end LiteralColoring

#print axioms LiteralColoring.indexWeight
#print axioms LiteralColoring.fullCycleType
#print axioms LiteralColoring.pointIndex_eq_iff
#print axioms LiteralColoring.pointIndex_surjective
#print axioms LiteralColoring.cyclesEquivIndex
#print axioms LiteralColoring.cyclesEquivIndex_apply
#print axioms LiteralColoring.cycleWeight_eq_indexWeight

#print axioms LiteralColoring.cycleWeights_eq_fullCycleType
```

## PairColor.lean

```lean
import CycleColor
import Mathlib.GroupTheory.GroupAction.Quotient

open scoped BigOperators

namespace LiteralColoring

noncomputable section

abbrev ColorPair {n ell r : ℕ} (a : Fin ell → ℕ) (b : Fin r → ℕ) :=
  Coloring (n := n) a × Coloring (n := n) b

abbrev PairOrbits {n ell r : ℕ} (a : Fin ell → ℕ) (b : Fin r → ℕ) :=
  Quotient (MulAction.orbitRel (Equiv.Perm (Fin n)) (ColorPair (n := n) a b))

abbrev Contingency {ell r : ℕ} (a : Fin ell → ℕ) (b : Fin r → ℕ) :=
  {M : Fin ell → Fin r → ℕ // (∀ i, ∑ j, M i j = a i) ∧ (∀ j, ∑ i, M i j = b j)}

def pairLabel {n ell r : ℕ} {a : Fin ell → ℕ} {b : Fin r → ℕ}
    (p : ColorPair (n := n) a b) (x : Fin n) : Fin ell × Fin r :=
  (p.1.val x, p.2.val x)

def cell {n ell r : ℕ} {a : Fin ell → ℕ} {b : Fin r → ℕ}
    (p : ColorPair (n := n) a b) (i : Fin ell) (j : Fin r) : ℕ :=
  Nat.card {x // pairLabel p x = (i, j)}

private theorem card_fiber_eq_sum {A B : Type*} [Finite A] [Fintype B] (p : A → B) :
    Nat.card A = ∑ b : B, Nat.card {x // p x = b} := by
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv p), Nat.card_sigma]

private def row_fiber {A I J : Type*} (f : A → I) (g : A → J) (i : I) (j : J) :
    {x : {x // f x = i} // g x.val = j} ≃ {x // (f x, g x) = (i, j)} where
  toFun x := ⟨x.val.val, Prod.ext x.val.property x.property⟩
  invFun x := ⟨⟨x.val, congrArg Prod.fst x.property⟩, congrArg Prod.snd x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def col_fiber {A I J : Type*} (f : A → I) (g : A → J) (i : I) (j : J) :
    {x : {x // g x = j} // f x.val = i} ≃ {x // (f x, g x) = (i, j)} where
  toFun x := ⟨x.val.val, Prod.ext x.property x.val.property⟩
  invFun x := ⟨⟨x.val, congrArg Prod.snd x.property⟩, congrArg Prod.fst x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def pairMatrix {n ell r : ℕ} {a : Fin ell → ℕ} {b : Fin r → ℕ}
    (p : ColorPair (n := n) a b) : Contingency a b :=
  ⟨cell p,
    ⟨fun i => (Finset.sum_congr rfl (fun j _ =>
        (Nat.card_congr (row_fiber p.1.val p.2.val i j)).symm)).trans
        ((card_fiber_eq_sum (fun x : {x // p.1.val x = i} => p.2.val x.val)).symm.trans
          (p.1.property i)),
     fun j => (Finset.sum_congr rfl (fun i _ =>
        (Nat.card_congr (col_fiber p.1.val p.2.val i j)).symm)).trans
        ((card_fiber_eq_sum (fun x : {x // p.2.val x = j} => p.1.val x.val)).symm.trans
          (p.2.property j))⟩⟩

theorem pairMatrix_smul {n ell r : ℕ} {a : Fin ell → ℕ} {b : Fin r → ℕ}
    (g : Equiv.Perm (Fin n)) (p : ColorPair (n := n) a b) :
    pairMatrix (g • p) = pairMatrix p := by
  apply Subtype.ext
  funext i j
  exact Nat.card_congr (g.symm.subtypeEquiv fun _ => Iff.rfl)

theorem exists_smul_of_pairMatrix_eq {n ell r : ℕ} {a : Fin ell → ℕ} {b : Fin r → ℕ}
    (p q : ColorPair (n := n) a b) (h : pairMatrix p = pairMatrix q) :
    ∃ g : Equiv.Perm (Fin n), g • p = q := by
  let e (v : Fin ell × Fin r) :
      {x // pairLabel p x = v} ≃ {x // pairLabel q x = v} :=
    by
      classical
      apply Fintype.equivOfCardEq
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      exact congrArg (fun M : Contingency a b => M.val v.1 v.2) h
  let g : Equiv.Perm (Fin n) :=
    (Equiv.sigmaFiberEquiv (pairLabel p)).symm.trans
      ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv (pairLabel q)))
  have hg (x : Fin n) : pairLabel q (g x) = pairLabel p x :=
    (e (pairLabel p x) ⟨x, rfl⟩).property
  have hi (x : Fin n) : pairLabel p (g⁻¹ x) = pairLabel q x := by
    simpa only [show g (g⁻¹ x) = x from g.apply_symm_apply x] using (hg (g⁻¹ x)).symm
  exact ⟨g, Prod.ext (Subtype.ext (funext fun x => congrArg Prod.fst (hi x)))
    (Subtype.ext (funext fun x => congrArg Prod.snd (hi x)))⟩

def orbitMatrix {n ell r : ℕ} {a : Fin ell → ℕ} {b : Fin r → ℕ} :
    PairOrbits (n := n) a b → Contingency a b :=
  Quotient.lift pairMatrix fun p q h => by
    obtain ⟨g, rfl⟩ := (MulAction.mem_orbit_iff.mp ((MulAction.orbitRel_apply).mp h))
    exact pairMatrix_smul g q

theorem orbitMatrix_injective {n ell r : ℕ} {a : Fin ell → ℕ} {b : Fin r → ℕ} :
    Function.Injective (orbitMatrix (n := n) (a := a) (b := b)) := by
  intro u v
  induction u using Quotient.inductionOn with
  | _ p =>
    induction v using Quotient.inductionOn with
    | _ q =>
      intro h
      obtain ⟨g, hg⟩ := exists_smul_of_pairMatrix_eq q p h.symm
      exact Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨g, hg⟩))

theorem pairMatrix_surjective {n ell r : ℕ} {a : Fin ell → ℕ} {b : Fin r → ℕ}
    (ha : ∑ i, a i = n) : Function.Surjective (pairMatrix (n := n) (a := a) (b := b)) := by
  intro M
  let T := Σ v : Fin ell × Fin r, Fin (M.val v.1 v.2)
  have hT : Nat.card T = Nat.card (Fin n) := by
    rw [Nat.card_sigma, Nat.card_fin, Fintype.sum_prod_type]
    simp only [Nat.card_fin]
    simpa only [M.property.1] using ha
  let e : Fin n ≃ T := Fintype.equivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hT.symm)
  let f (x : Fin n) : Fin ell := (e x).1.1
  let g (x : Fin n) : Fin r := (e x).1.2
  have hc (i : Fin ell) (j : Fin r) :
      Nat.card {x // (f x, g x) = (i, j)} = M.val i j := by
    let fiber : {x : T // x.1 = (i, j)} ≃ Fin (M.val i j) :=
      { toFun := fun x => Fin.cast (congrArg (fun v : Fin ell × Fin r => M.val v.1 v.2) x.property) x.val.2
        invFun := fun z => ⟨⟨(i,j), z⟩, rfl⟩
        left_inv := by rintro ⟨⟨v,z⟩, hv⟩; change v = (i,j) at hv; subst v; rfl
        right_inv := fun _ => rfl }
    rw [← Nat.card_fin (M.val i j)]
    exact Nat.card_congr ((e.subtypeEquiv fun _ => Iff.rfl).trans fiber)
  have hf (i : Fin ell) : margin f i = a i := by
    rw [margin, card_fiber_eq_sum (fun x : {x // f x = i} => g x.val)]
    simp_rw [Nat.card_congr (row_fiber f g i _), hc]
    exact M.property.1 i
  have hg (j : Fin r) : margin g j = b j := by
    rw [margin, card_fiber_eq_sum (fun x : {x // g x = j} => f x.val)]
    simp_rw [Nat.card_congr (col_fiber f g _ j), hc]
    exact M.property.2 j
  exact ⟨(⟨f, hf⟩, ⟨g, hg⟩), Subtype.ext (funext fun i => funext fun j => hc i j)⟩

def pairOrbitEquivContingency {n ell r : ℕ} {a : Fin ell → ℕ} {b : Fin r → ℕ}
    (ha : ∑ i, a i = n) : PairOrbits (n := n) a b ≃ Contingency a b :=
  Equiv.ofBijective orbitMatrix ⟨orbitMatrix_injective, fun M => by
    obtain ⟨p, hp⟩ := pairMatrix_surjective ha M
    exact ⟨Quotient.mk _ p, hp⟩⟩

theorem pairOrbit_card {n ell r : ℕ} {a : Fin ell → ℕ} {b : Fin r → ℕ}
    (ha : ∑ i, a i = n) : Nat.card (PairOrbits (n := n) a b) = Nat.card (Contingency a b) :=
  Nat.card_congr (pairOrbitEquivContingency ha)

end

end LiteralColoring

#print axioms LiteralColoring.pairLabel
#print axioms LiteralColoring.cell
#print axioms LiteralColoring.pairMatrix
#print axioms LiteralColoring.pairMatrix_smul
#print axioms LiteralColoring.exists_smul_of_pairMatrix_eq
#print axioms LiteralColoring.orbitMatrix
#print axioms LiteralColoring.orbitMatrix_injective
#print axioms LiteralColoring.pairMatrix_surjective
#print axioms LiteralColoring.pairOrbitEquivContingency
#print axioms LiteralColoring.pairOrbit_card
```

## ColorPairing.lean

```lean
import PairColor

open scoped BigOperators

namespace LiteralColoring

noncomputable section

def fixedPairEquiv {n ell r : ℕ} {a : Fin ell → ℕ} {b : Fin r → ℕ}
    (g : Equiv.Perm (Fin n)) :
    MulAction.fixedBy (ColorPair (n := n) a b) g ≃ FixedColorings g a × FixedColorings g b where
  toFun p := (⟨p.val.1, congrArg Prod.fst p.property⟩, ⟨p.val.2, congrArg Prod.snd p.property⟩)
  invFun p := ⟨(p.1.val, p.2.val), Prod.ext p.1.property p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem coloring_character_inv {n ell : ℕ} (a : Fin ell → ℕ) (g : Equiv.Perm (Fin n)) :
    (coloringRep a).character g⁻¹ = (coloringRep a).character g := by
  rw [character_eq_fixed, character_eq_fixed]
  exact congrArg (fun x : ℕ => (x : ℂ)) (Nat.card_congr
    ((Equiv.refl _).subtypeEquiv fun f => inv_smul_eq_iff.trans eq_comm))

theorem sum_coloring_characters_mul {n ell r : ℕ} (a : Fin ell → ℕ) (b : Fin r → ℕ)
    (ha : ∑ i, a i = n) :
    ∑ g : Equiv.Perm (Fin n), (coloringRep a).character g * (coloringRep b).character g⁻¹ =
      (Nat.card (Contingency a b) : ℂ) * (Fintype.card (Equiv.Perm (Fin n)) : ℂ) := by
  classical
  let _ (g : Equiv.Perm (Fin n)) := Fintype.ofFinite (MulAction.fixedBy (ColorPair (n := n) a b) g)
  let _ := Fintype.ofFinite (PairOrbits (n := n) a b)
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (Equiv.Perm (Fin n)) (ColorPair (n := n) a b)
  have hfix (g : Equiv.Perm (Fin n)) :
      (coloringRep a).character g * (coloringRep b).character g⁻¹ =
        (Fintype.card (MulAction.fixedBy (ColorPair (n := n) a b) g) : ℂ) := by
    rw [coloring_character_inv b, character_eq_fixed, character_eq_fixed, ← Nat.cast_mul,
      ← Nat.card_prod, ← Nat.card_congr (fixedPairEquiv g), Nat.card_eq_fintype_card]
  simp_rw [hfix]
  rw [← Nat.cast_sum, h, Nat.cast_mul, ← Nat.card_eq_fintype_card, pairOrbit_card ha]

theorem coloring_pairing_eq_contingency {n ell r : ℕ} (a : Fin ell → ℕ) (b : Fin r → ℕ)
    (ha : ∑ i, a i = n) :
    (Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ *
      (∑ g : Equiv.Perm (Fin n), (coloringRep a).character g * (coloringRep b).character g⁻¹) =
      (Nat.card (Contingency a b) : ℂ) := by
  rw [sum_coloring_characters_mul a b ha, mul_comm (Nat.card _ : ℂ), ← mul_assoc,
    inv_mul_cancel₀, one_mul]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

end

end LiteralColoring

#print axioms LiteralColoring.fixedPairEquiv
#print axioms LiteralColoring.coloring_character_inv
#print axioms LiteralColoring.sum_coloring_characters_mul
#print axioms LiteralColoring.coloring_pairing_eq_contingency
```

## CycleCoefficient.lean

```lean
import CycleTypeColor
import Mathlib.Algebra.MvPolynomial.Basic

open scoped BigOperators

namespace LiteralColoring

noncomputable section

def powerSum (ell m : ℕ) : MvPolynomial (Fin ell) ℂ :=
  ∑ i : Fin ell, MvPolynomial.X i ^ m

def exponent {ell : ℕ} (a : Fin ell → ℕ) : Fin ell →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm a

def cyclePowerProduct (n ell : ℕ) (g : Equiv.Perm (Fin n)) :
    MvPolynomial (Fin ell) ℂ :=
  ((fullCycleType g).map (powerSum ell)).prod

private theorem assignment_exp {n ell : ℕ} (g : Equiv.Perm (Fin n))
    (c : Cycles g → Fin ell) :
    (let _ := Fintype.ofFinite (Cycles g)
     ∑ j, Finsupp.single (c j) (cycleWeight g j)) = exponent (cycleMargin c) := by
  classical
  let _ := Fintype.ofFinite (Cycles g)
  ext i
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, exponent,
    Finsupp.equivFunOnFinite_symm_apply_apply, cycleMargin]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun _ => by simp) _

theorem character_eq_cycle_coefficient {n ell : ℕ} (g : Equiv.Perm (Fin n)) (a : Fin ell → ℕ) :
    (coloringRep a).character g = (cyclePowerProduct n ell g).coeff (exponent a) := by
  classical
  let _ := Fintype.ofFinite (Cycles g)
  let _ := Fintype.ofFinite (CycleColorings g a)
  have hpoly : cyclePowerProduct n ell g = ∏ j : Cycles g, powerSum ell (cycleWeight g j) := by
    rw [cyclePowerProduct, ← cycleWeights_eq_fullCycleType, cycleWeights, Multiset.map_map,
      Finset.prod_map_val]
    rfl
  rw [character_eq_cycleColorings, hpoly]
  simp only [powerSum]
  rw [Fintype.prod_sum]
  simp_rw [MvPolynomial.X_pow_eq_monomial, ← MvPolynomial.monomial_sum_one, assignment_exp g,
    MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  have h (c : Cycles g → Fin ell) :
      exponent (cycleMargin c) = exponent a ↔ ∀ i, cycleMargin c i = a i := by
    change Finsupp.equivFunOnFinite.symm (cycleMargin c) = Finsupp.equivFunOnFinite.symm a ↔ _
    rw [Finsupp.equivFunOnFinite.symm.injective.eq_iff]
    exact ⟨fun hc i => congrFun hc i, fun hc => funext hc⟩
  simp_rw [h]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_one, Nat.card_eq_fintype_card]
  congr 1
  rw [Fintype.card_subtype]

end

end LiteralColoring

#print axioms LiteralColoring.powerSum
#print axioms LiteralColoring.exponent
#print axioms LiteralColoring.cyclePowerProduct
#print axioms LiteralColoring.character_eq_cycle_coefficient
```

## LiteralPermutationCharacter.lean

```lean
import CycleCoefficient
import ColorPairing

open scoped BigOperators

namespace LiteralColoring

theorem fullCycleType_padding {m n : ℕ} (g : Equiv.Perm (Fin m)) (h : Equiv.Perm (Fin n))
    (hmn : m ≤ n) (hcycle : g.cycleType = h.cycleType) :
    fullCycleType h = fullCycleType g + Multiset.replicate (n - m) 1 := by
  have hs := congrArg Multiset.sum hcycle
  rw [Equiv.Perm.sum_cycleType, Equiv.Perm.sum_cycleType] at hs
  have hle : g.support.card ≤ m := by simpa using g.support.card_le_univ
  have hpad : n - h.support.card = (m - g.support.card) + (n - m) := by omega
  rw [fullCycleType, fullCycleType, ← hcycle, hpad, Multiset.replicate_add, add_assoc]

theorem character_eq_of_cycleType_eq {n ell : ℕ} (a : Fin ell → ℕ)
    (g h : Equiv.Perm (Fin n)) (hcycle : g.cycleType = h.cycleType) :
    (coloringRep a).character g = (coloringRep a).character h := by
  have hp := fullCycleType_padding g h le_rfl hcycle
  rw [Nat.sub_self, Multiset.replicate_zero, add_zero] at hp
  rw [character_eq_cycle_coefficient, character_eq_cycle_coefficient, cyclePowerProduct,
    cyclePowerProduct, hp]

end LiteralColoring

#print axioms LiteralColoring.fullCycleType_padding
#print axioms LiteralColoring.character_eq_of_cycleType_eq
#check LiteralColoring.coloringRep
#check LiteralColoring.character_eq_fixed
#check LiteralColoring.fixedEquivCycles
#check LiteralColoring.cycleWeights_eq_fullCycleType
#check LiteralColoring.character_eq_cycle_coefficient
#check LiteralColoring.pairMatrix_smul
#check LiteralColoring.exists_smul_of_pairMatrix_eq
#check LiteralColoring.pairMatrix_surjective
#check LiteralColoring.pairOrbitEquivContingency
#check LiteralColoring.coloring_pairing_eq_contingency
#check LiteralColoring.fullCycleType_padding
#check LiteralColoring.character_eq_of_cycleType_eq
```

## SignedAlternant.lean

```lean
import LiteralPermutationCharacter
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open scoped BigOperators
open MvPolynomial
open Equiv.Perm

namespace LiteralColoring

noncomputable section

def descendingOffset {ell : ℕ} (i : Fin ell) : ℕ := ell - 1 - i.val

def integerShift {ell : ℕ} (u : Fin ell → ℕ) (σ : Equiv.Perm (Fin ell))
    (i : Fin ell) : ℤ := (u i : ℤ) - (descendingOffset (σ i) : ℤ)

def ValidShift {ell : ℕ} (u : Fin ell → ℕ) (σ : Equiv.Perm (Fin ell)) : Prop :=
  ∀ i, 0 ≤ integerShift u σ i

def shiftedMargin {ell : ℕ} (u : Fin ell → ℕ) (σ : Equiv.Perm (Fin ell)) (i : Fin ell) : ℕ :=
  (integerShift u σ i).toNat

theorem validShift_iff {ell : ℕ} (u : Fin ell → ℕ) (σ : Equiv.Perm (Fin ell)) :
    ValidShift u σ ↔ ∀ i, descendingOffset (σ i) ≤ u i := by
  simp [ValidShift, integerShift]

theorem shiftedMargin_add_offset {ell : ℕ} (u : Fin ell → ℕ) (σ : Equiv.Perm (Fin ell))
    (h : ValidShift u σ) (i : Fin ell) :
    shiftedMargin u σ i + descendingOffset (σ i) = u i := by
  have hi := Int.toNat_of_nonneg (h i)
  change (shiftedMargin u σ i : ℤ) = _ at hi
  unfold integerShift at hi
  omega

theorem shiftedMargin_sum {n ell : ℕ} (u : Fin ell → ℕ) (σ : Equiv.Perm (Fin ell))
    (hu : ∑ i, u i = n + ∑ i : Fin ell, descendingOffset i) (h : ValidShift u σ) :
    ∑ i, shiftedMargin u σ i = n := by
  have he := Finset.sum_congr (s₁ := Finset.univ) rfl
    (fun i _ => shiftedMargin_add_offset u σ h i)
  rw [Finset.sum_add_distrib, Equiv.sum_comp σ descendingOffset, hu] at he
  exact Nat.add_right_cancel he

def signedWeight {ell : ℕ} (u : Fin ell → ℕ) (σ : Equiv.Perm (Fin ell)) : ℂ := by
  classical
  exact if ValidShift u σ then ((sign σ : ℤ) : ℂ) else 0

def signedCharacter (n : ℕ) {ell : ℕ} (u : Fin ell → ℕ) (g : Equiv.Perm (Fin n)) : ℂ :=
  ∑ σ : Equiv.Perm (Fin ell), signedWeight u σ * (coloringRep (shiftedMargin u σ)).character g

def descendingVandermonde (ell : ℕ) : MvPolynomial (Fin ell) ℂ :=
  (Matrix.of fun i j : Fin ell => (X j : MvPolynomial (Fin ell) ℂ) ^ descendingOffset i).det

theorem descendingVandermonde_expansion (ell : ℕ) :
    descendingVandermonde ell = ∑ σ : Equiv.Perm (Fin ell),
      monomial (exponent (descendingOffset ∘ σ)) ((sign σ : ℤ) : ℂ) := by
  classical
  rw [descendingVandermonde, Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Matrix.of_apply, X_pow_eq_monomial, ← monomial_sum_one]
  have he : (∑ i : Fin ell, Finsupp.single i (descendingOffset (σ i))) =
      exponent (descendingOffset ∘ σ) := by
    ext j
    simp [Finsupp.finsetSum_apply, Finsupp.single_apply, exponent]
  rw [he]
  rw [← map_intCast (C : ℂ →+* MvPolynomial (Fin ell) ℂ), C_mul_monomial, mul_one]

theorem coeff_shifted_monomial {ell : ℕ} (u : Fin ell → ℕ) (σ : Equiv.Perm (Fin ell))
    (P : MvPolynomial (Fin ell) ℂ) :
    (monomial (exponent (descendingOffset ∘ σ)) ((sign σ : ℤ) : ℂ) * P).coeff (exponent u) =
      signedWeight u σ * P.coeff (exponent (shiftedMargin u σ)) := by
  classical
  by_cases h : ValidShift u σ
  · have he : exponent u = exponent (descendingOffset ∘ σ) + exponent (shiftedMargin u σ) := by
      ext i
      change u i = descendingOffset (σ i) + shiftedMargin u σ i
      rw [add_comm, shiftedMargin_add_offset u σ h i]
    simp only [signedWeight, ite_eq_left h]
    conv_lhs => rw [he]
    exact coeff_monomial_mul _ _ _ _
  · simp only [signedWeight, ite_eq_right h, zero_mul]
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    intro q hq
    rw [coeff_monomial]
    split_ifs with he
    · exfalso
      apply h
      rw [validShift_iff]
      intro i
      have hs := congrArg (fun d : Fin ell →₀ ℕ => d i) (Finset.mem_antidiagonal.mp hq)
      change q.1 i + q.2 i = u i at hs
      have hc := congrArg (fun d : Fin ell →₀ ℕ => d i) he
      change descendingOffset (σ i) = q.1 i at hc
      omega
    · exact zero_mul _

theorem signedCharacter_eq_coefficient {n ell : ℕ} (u : Fin ell → ℕ)
    (g : Equiv.Perm (Fin n)) :
    signedCharacter n u g =
      (descendingVandermonde ell * cyclePowerProduct n ell g).coeff (exponent u) := by
  classical
  rw [descendingVandermonde_expansion, Finset.sum_mul, coeff_sum, signedCharacter]
  simp_rw [coeff_shifted_monomial, character_eq_cycle_coefficient]

end

end LiteralColoring

#print axioms LiteralColoring.shiftedMargin_sum
#print axioms LiteralColoring.descendingVandermonde_expansion
#print axioms LiteralColoring.coeff_shifted_monomial
#print axioms LiteralColoring.signedCharacter_eq_coefficient
```

## SignedPairing.lean

```lean
import SignedAlternant

open scoped BigOperators

namespace LiteralColoring

noncomputable section

def normalizedPairing {G : Type*} [Group G] [Fintype G] (f g : G → ℂ) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ h : G, f h * g h⁻¹

theorem normalizedPairing_weighted {G A B : Type*} [Group G] [Fintype G]
    [Fintype A] [Fintype B] (w : A → ℂ) (z : B → ℂ) (f : A → G → ℂ) (g : B → G → ℂ) :
    normalizedPairing (fun h => ∑ a, w a * f a h) (fun h => ∑ b, z b * g b h) =
      ∑ a, ∑ b, w a * z b * normalizedPairing (f a) (g b) := by
  unfold normalizedPairing
  simp only [Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset B)) (t := (Finset.univ : Finset A)),
    Finset.sum_comm (s := (Finset.univ : Finset G)) (t := (Finset.univ : Finset A)),
    Finset.sum_comm (s := (Finset.univ : Finset G)) (t := (Finset.univ : Finset B))]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro h hh
  ring

def signedContingency {ell : ℕ} (u v : Fin ell → ℕ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin ell), ∑ τ : Equiv.Perm (Fin ell),
    signedWeight u σ * signedWeight v τ *
      (Nat.card (Contingency (shiftedMargin u σ) (shiftedMargin v τ)) : ℂ)

theorem normalizedPairing_signedCharacter {n ell : ℕ} (u v : Fin ell → ℕ)
    (hu : ∑ i, u i = n + ∑ i : Fin ell, descendingOffset i)
    (hv : ∑ i, v i = n + ∑ i : Fin ell, descendingOffset i) :
    normalizedPairing (signedCharacter n u) (signedCharacter n v) = signedContingency u v := by
  classical
  change normalizedPairing
    (fun h => ∑ σ, signedWeight u σ * (coloringRep (shiftedMargin u σ)).character h)
    (fun h => ∑ τ, signedWeight v τ * (coloringRep (shiftedMargin v τ)).character h) = _
  rw [normalizedPairing_weighted, signedContingency]
  apply Finset.sum_congr rfl
  intro σ hσ
  apply Finset.sum_congr rfl
  intro τ hτ
  by_cases hs : ValidShift u σ
  · by_cases ht : ValidShift v τ
    · have ha := shiftedMargin_sum u σ hu hs
      have hb := shiftedMargin_sum v τ hv ht
      have hpair (a b : Fin ell → ℕ) (h : (∑ i, a i = n) ∧ (∑ i, b i = n)) :
          normalizedPairing (coloringRep a).character (coloringRep b).character =
            (Nat.card (Contingency a b) : ℂ) := coloring_pairing_eq_contingency a b h.1
      rw [hpair _ _ ⟨ha, hb⟩]
    · simp [signedWeight, ht]
  · simp [signedWeight, hs]

theorem twice_offset_sum (ell : ℕ) :
    2 * (∑ i : Fin ell, descendingOffset i) = ell * (ell - 1) := by
  induction ell with
  | zero => simp
  | succ ell ih =>
    rw [Fin.sum_univ_succ]
    have hzero : descendingOffset (0 : Fin (ell + 1)) = ell := by
      simp [descendingOffset]
    have hs (i : Fin ell) : descendingOffset i.succ = descendingOffset i := by
      simp only [descendingOffset, Nat.add_sub_cancel, Fin.val_succ]
      omega
    simp_rw [hzero, hs]
    rw [Nat.mul_add, ih, Nat.succ_sub_one, Nat.succ_mul]
    cases ell with
    | zero => simp
    | succ k =>
      rw [Nat.succ_sub_one]
      ring

theorem offset_sum (ell : ℕ) :
    (∑ i : Fin ell, descendingOffset i) = ell * (ell - 1) / 2 := by
  have := twice_offset_sum ell
  omega

end

end LiteralColoring

#print axioms LiteralColoring.normalizedPairing_weighted
#print axioms LiteralColoring.normalizedPairing_signedCharacter
#print axioms LiteralColoring.offset_sum
```

## ContingencyCoefficients.lean

```lean
import SignedPairing
import GeometricCoefficients

open scoped BigOperators
open MvPowerSeries Equiv.Perm

namespace LiteralColoring

noncomputable section

abbrev GridIndex (ell : ℕ) := Fin ell ⊕ Fin ell

def gridExponent {ell : ℕ} (a b : Fin ell → ℕ) : GridIndex ell →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Sum.elim a b)

@[simp] theorem gridExponent_left {ell : ℕ} (a b : Fin ell → ℕ) (i : Fin ell) :
    gridExponent a b (Sum.inl i) = a i := rfl

@[simp] theorem gridExponent_right {ell : ℕ} (a b : Fin ell → ℕ) (i : Fin ell) :
    gridExponent a b (Sum.inr i) = b i := rfl

def cellExponent {ell : ℕ} (i j : Fin ell) : GridIndex ell →₀ ℕ :=
  Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr j) 1

@[simp] theorem cellExponent_left {ell : ℕ} (i j p : Fin ell) (k : ℕ) :
    (k • cellExponent i j) (Sum.inl p) = if i = p then k else 0 := by
  classical
  by_cases h : i = p <;> simp [cellExponent, h]

@[simp] theorem cellExponent_right {ell : ℕ} (i j p : Fin ell) (k : ℕ) :
    (k • cellExponent i j) (Sum.inr p) = if j = p then k else 0 := by
  classical
  by_cases h : j = p <;> simp [cellExponent, h]

theorem cellExponent_injective {ell : ℕ} (i j : Fin ell) :
    Function.Injective (fun k : ℕ => k • cellExponent i j) := by
  intro a b h
  simpa using congrArg (fun d : GridIndex ell →₀ ℕ => d (Sum.inl i)) h

def gridKernel {ell : ℕ} : Matrix (Fin ell) (Fin ell) (MvPowerSeries (GridIndex ell) ℂ) :=
  Matrix.of fun i j => geometric (cellExponent i j)

theorem gridKernel_inverse {ell : ℕ} (i j : Fin ell) :
    gridKernel i j * (1 - X (Sum.inl i) * X (Sum.inr j)) = 1 := by
  classical
  change geometric (cellExponent i j) * _ = 1
  rw [X, X, monomial_mul_monomial, one_mul]
  apply geometric_mul_sub
  intro h
  have hz := congrArg (fun d : GridIndex ell →₀ ℕ => d (Sum.inl i)) h
  have ho : cellExponent i j (Sum.inl i) = 1 := by
    simpa only [one_nsmul, ite_eq_left rfl, ite_true] using cellExponent_left i j i 1
  simp [ho] at hz

def gridProduct (ell : ℕ) : MvPowerSeries (GridIndex ell) ℂ :=
  ∏ i : Fin ell, ∏ j : Fin ell, gridKernel i j

private theorem weights_margins {ell : ℕ} (a b : Fin ell → ℕ)
    (k : Fin ell × Fin ell → ℕ) :
    (∑ p, k p • cellExponent p.1 p.2 = gridExponent a b) ↔
      (∀ i, ∑ j, k (i,j) = a i) ∧ (∀ j, ∑ i, k (i,j) = b j) := by
  classical
  have hleft (i : Fin ell) :
      (∑ p, k p • cellExponent p.1 p.2) (Sum.inl i) = ∑ j, k (i,j) := by
    simp only [Finsupp.finsetSum_apply, cellExponent_left, Fintype.sum_prod_type]
    calc
      _ = ∑ p : Fin ell, if p = i then ∑ j, k (p,j) else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        by_cases h : p = i <;> simp [h]
      _ = _ := by simp
  have hright (j : Fin ell) :
      (∑ p, k p • cellExponent p.1 p.2) (Sum.inr j) = ∑ i, k (i,j) := by
    simp only [Finsupp.finsetSum_apply, cellExponent_right, Fintype.sum_prod_type]
    simp
  constructor
  · intro h
    exact ⟨fun i => (hleft i).symm.trans (congrArg (fun d => d (Sum.inl i)) h),
      fun j => (hright j).symm.trans (congrArg (fun d => d (Sum.inr j)) h)⟩
  · rintro ⟨ha,hb⟩
    ext p
    cases p with
    | inl i => exact (hleft i).trans (ha i)
    | inr j => exact (hright j).trans (hb j)

theorem coeff_gridProduct {ell : ℕ} (a b : Fin ell → ℕ) :
    coeff (gridExponent a b) (gridProduct ell) = (Nat.card (Contingency a b) : ℂ) := by
  classical
  let E (p : Fin ell × Fin ell) := cellExponent p.1 p.2
  change coeff _ (∏ i : Fin ell, ∏ j : Fin ell, geometric (E (i,j))) = _
  have hp := Fintype.prod_prod_type (fun p : Fin ell × Fin ell => geometric (E p))
  rw [← hp, coeff_prod_geometric E (fun p => cellExponent_injective p.1 p.2)]
  exact congrArg (fun n : ℕ => (n : ℂ)) (Nat.card_congr
    { toFun := fun k => ⟨fun i j => k.val (i,j), (weights_margins a b k.val).mp k.property⟩
      invFun := fun m => ⟨fun p => m.val p.1 p.2, (weights_margins a b _).mpr m.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl })

end

end LiteralColoring

#print axioms LiteralColoring.gridKernel_inverse
#print axioms LiteralColoring.coeff_gridProduct
```

## VandermondeSigns.lean

```lean
import SignedPairing
import CauchyDeterminant
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Data.Fin.Rev

open scoped BigOperators
open Matrix Equiv.Perm

namespace LiteralColoring

private theorem prod_Ioi_succ {R : Type*} [CommMonoid R] {n : ℕ}
    (i : Fin n) (f : Fin (n + 1) → R) :
    (∏ j ∈ Finset.Ioi i.succ, f j) = ∏ j ∈ Finset.Ioi i, f j.succ := by
  symm
  refine Finset.prod_bij (fun j _ => j.succ) (fun j hj => ?_) (fun a _ b _ h => ?_)
    (fun j hj => ?_) (fun _ _ => rfl)
  · simpa only [Finset.mem_Ioi, Fin.succ_lt_succ_iff] using hj
  · exact Fin.succ_injective _ h
  · revert hj
    refine Fin.cases ?_ (fun k hk => ?_) j
    · simp
    · exact ⟨k, by simpa only [Finset.mem_Ioi, Fin.succ_lt_succ_iff] using hk, rfl⟩

private theorem prod_Ioi_zero {R : Type*} [CommMonoid R] {n : ℕ}
    (f : Fin (n + 1) → R) :
    (∏ j ∈ Finset.Ioi (0 : Fin (n + 1)), f j) = ∏ j : Fin n, f j.succ := by
  symm
  refine Finset.prod_bij (fun j _ => j.succ) (fun j hj => by simp)
    (fun a _ b _ h => Fin.succ_injective _ h) (fun j hj => ?_) (fun _ _ => rfl)
  revert hj
  refine Fin.cases ?_ (fun k hk => ?_) j
  · simp
  · exact ⟨k, Finset.mem_univ _, rfl⟩

theorem vandermondeFactors_eq_det {R : Type*} [CommRing R] {n : ℕ} (x : Fin n → R) :
    vandermondeFactors x = (Matrix.vandermonde x).det := by
  rw [Matrix.det_vandermonde]
  induction n with
  | zero => simp [vandermondeFactors]
  | succ n ih =>
    rw [vandermondeFactors, Fin.prod_univ_succ, prod_Ioi_zero, ih]
    simp_rw [prod_Ioi_succ]

def descendingDet {R : Type*} [CommRing R] {n : ℕ} (x : Fin n → R) : R :=
  (Matrix.of fun i j : Fin n => x j ^ descendingOffset i).det

theorem descendingDet_mul {R : Type*} [CommRing R] {n : ℕ} (x y : Fin n → R) :
    descendingDet x * descendingDet y = vandermondeFactors x * vandermondeFactors y := by
  let r : Equiv.Perm (Fin n) := Fin.revPerm
  have h (z : Fin n → R) :
      descendingDet z = ((sign r : ℤ) : R) * (Matrix.vandermonde z).det := by
    rw [descendingDet, ← Matrix.det_transpose]
    have he : (Matrix.of fun i j : Fin n => z j ^ descendingOffset i)ᵀ =
        (Matrix.vandermonde z).submatrix id r := by
      ext i j
      change z i ^ descendingOffset j = z i ^ (r j).val
      congr 1
      change n - 1 - j.val = n - (j.val + 1)
      omega
    rw [he]
    exact Matrix.det_permute' r (Matrix.vandermonde z)
  have hr : r * r = 1 := by
    apply Equiv.ext
    intro i
    exact Fin.rev_rev i
  have hsign : ((sign r : ℤ) : R) * ((sign r : ℤ) : R) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, ← sign_mul, hr, sign_one]
    simp
  rw [h, h, vandermondeFactors_eq_det, vandermondeFactors_eq_det, mul_mul_mul_comm, hsign, one_mul]

end LiteralColoring

#print axioms LiteralColoring.vandermondeFactors_eq_det
#print axioms LiteralColoring.descendingDet_mul
```

## VirtualNorm.lean

```lean
import SignedPairing
import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.Analysis.Complex.Polynomial.Basic

open scoped BigOperators
open CategoryTheory

namespace LiteralColoring

noncomputable section

open scoped Classical in
theorem simple_pairing {G : Type*} [Group G] [Fintype G] (V W : FDRep ℂ G)
    [Simple V] [Simple W] :
    normalizedPairing V.character W.character = if Nonempty (V ≅ W) then 1 else 0 := by
  classical
  let _ := invertibleOfNonzero
    (a := (Nat.card G : ℂ))
    (by rw [Nat.card_eq_fintype_card]; exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  simpa [normalizedPairing, Nat.card_eq_fintype_card] using FDRep.char_orthonormal V W

theorem virtual_norm_distinct_simples {G I : Type*} [Group G] [Fintype G] [Fintype I]
    (V : I → FDRep ℂ G) (hs : ∀ i, Simple (V i))
    (hd : ∀ i j, Nonempty (V i ≅ V j) → i = j) (c : I → ℤ) :
    normalizedPairing (fun h => ∑ i, (c i : ℂ) * (V i).character h)
      (fun h => ∑ i, (c i : ℂ) * (V i).character h) =
      ((∑ i, c i ^ 2 : ℤ) : ℂ) := by
  classical
  rw [normalizedPairing_weighted]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · let _ := hs i
    rw [simple_pairing, ite_eq_left (show Nonempty (V i ≅ V i) from ⟨Iso.refl _⟩), mul_one, pow_two]
  · intro j hj hji
    let _ := hs i
    let _ := hs j
    rw [simple_pairing, ite_eq_right (fun h => hji (hd i j h).symm), mul_zero]
  · simp

private theorem int_square_sum_one {I : Type*} [Fintype I] (c : I → ℤ)
    (h : ∑ i, c i ^ 2 = 1) :
    ∃ i, (c i = 1 ∨ c i = -1) ∧ ∀ j, j ≠ i → c j = 0 := by
  classical
  have hex : ∃ i, c i ≠ 0 := by
    by_contra! hn
    simp [hn] at h
  obtain ⟨i, hi⟩ := hex
  have er := Finset.sum_erase_add (s := Finset.univ) (fun i => c i ^ 2) (Finset.mem_univ i)
  have hnn : 0 ≤ ∑ j ∈ Finset.univ.erase i, c j ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs : 1 ≤ c i ^ 2 := by
    have hpos : 0 < c i ^ 2 := sq_pos_of_ne_zero hi
    omega
  have hzero : ∑ j ∈ Finset.univ.erase i, c j ^ 2 = 0 := by omega
  have h1 : c i ^ 2 = 1 := by omega
  refine ⟨i, ?_, fun j hj => ?_⟩
  · have hz : (c i - 1) * (c i + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hz with ha | hb
    · left
      omega
    · right
      omega
  · have hj' : j ∈ Finset.univ.erase i := by simp [hj]
    have hle := Finset.single_le_sum (fun k _ => sq_nonneg (c k)) hj'
    rw [hzero] at hle
    exact by
      by_contra hne
      exact (not_lt_of_ge hle) (sq_pos_of_ne_zero hne)

theorem virtual_norm_one_up_to_sign {G I : Type*} [Group G] [Fintype G] [Fintype I]
    (V : I → FDRep ℂ G) (hs : ∀ i, Simple (V i))
    (hd : ∀ i j, Nonempty (V i ≅ V j) → i = j) (c : I → ℤ)
    (f : G → ℂ) (hf : f = fun h => ∑ i, (c i : ℂ) * (V i).character h)
    (hn : normalizedPairing f f = 1) :
    ∃ W : FDRep ℂ G, Simple W ∧ (f = W.character ∨ f = -W.character) := by
  classical
  have hn' : (∑ i, c i ^ 2) = 1 := by
    rw [hf, virtual_norm_distinct_simples V hs hd c] at hn
    exact_mod_cast hn
  obtain ⟨i, hi, hz⟩ := int_square_sum_one c hn'
  refine ⟨V i, hs i, ?_⟩
  have hfun : f = fun h => (c i : ℂ) * (V i).character h := by
    funext h
    rw [hf]
    change (∑ j, (c j : ℂ) * (V j).character h) = _
    rw [Finset.sum_eq_single i]
    · intro j hj hji
      simp [hz j hji]
    · simp
  rcases hi with hi | hi
  · left
    simp [hfun, hi]
  · right
    funext h
    simp [hfun, hi]

end

end LiteralColoring

#print axioms LiteralColoring.simple_pairing
#print axioms LiteralColoring.virtual_norm_distinct_simples
#print axioms LiteralColoring.virtual_norm_one_up_to_sign
```

## CauchyDiagonal.lean

```lean
import ContingencyCoefficients
import Mathlib.Order.Preorder.Finite

open scoped BigOperators
open MvPowerSeries Equiv.Perm

namespace LiteralColoring

noncomputable section

theorem matching_weights {ell : ℕ} (u v : Fin ell → ℕ) (σ : Equiv.Perm (Fin ell))
    (k : Fin ell → ℕ) :
    (∑ j, k j • cellExponent (σ j) j = gridExponent u v) ↔
      (∀ j, k j = v j) ∧ (∀ j, u (σ j) = v j) := by
  classical
  have hl (p : Fin ell) :
      (∑ j, k j • cellExponent (σ j) j) (Sum.inl p) = k (σ.symm p) := by
    simp only [Finsupp.finsetSum_apply, cellExponent_left]
    rw [Finset.sum_eq_single (σ.symm p)]
    · simp
    · intro j hj hn
      exact ite_eq_right (fun h : σ j = p => hn (σ.injective (h.trans (σ.apply_symm_apply p).symm)))
    · simp
  have hr (j : Fin ell) : (∑ p, k p • cellExponent (σ p) p) (Sum.inr j) = k j := by
    simp only [Finsupp.finsetSum_apply, cellExponent_right]
    simp
  constructor
  · intro h
    have hv (j : Fin ell) : k j = v j :=
      (hr j).symm.trans (congrArg (fun d => d (Sum.inr j)) h)
    refine ⟨hv, fun j => ?_⟩
    have hj := congrArg (fun d : GridIndex ell →₀ ℕ => d (Sum.inl (σ j))) h
    rw [hl, gridExponent_left, σ.symm_apply_apply] at hj
    exact hj.symm.trans (hv j)
  · rintro ⟨hk,huv⟩
    ext p
    cases p with
    | inl i =>
      rw [hl, gridExponent_left, hk, ← huv, σ.apply_symm_apply]
    | inr j => exact (hr j).trans (hk j)

theorem coeff_matchingProduct {ell : ℕ} (u v : Fin ell → ℕ) (σ : Equiv.Perm (Fin ell)) :
    coeff (gridExponent u v) (∏ j, gridKernel (σ j) j) =
      if ∀ j, u (σ j) = v j then 1 else 0 := by
  classical
  change coeff _ (∏ j, geometric (cellExponent (σ j) j)) = _
  rw [coeff_prod_geometric _ (fun j => cellExponent_injective (σ j) j)]
  by_cases h : ∀ j, u (σ j) = v j
  · rw [ite_eq_left h]
    have hc : Nat.card (WeightFiber (fun j => cellExponent (σ j) j) (gridExponent u v)) = 1 := by
      rw [Nat.card_eq_one_iff_exists]
      refine ⟨⟨v, (matching_weights u v σ v).mpr ⟨fun _ => rfl, h⟩⟩, fun k => ?_⟩
      exact Subtype.ext (funext ((matching_weights u v σ k.val).mp k.property).1)
    simp [hc]
  · rw [ite_eq_right h]
    have he : IsEmpty (WeightFiber (fun j => cellExponent (σ j) j) (gridExponent u v)) :=
      ⟨fun k => h ((matching_weights u v σ k.val).mp k.property).2⟩
    let _ := he
    simp

theorem coeff_gridKernel_det {ell : ℕ} (u v : Fin ell → ℕ)
    (hu : StrictAnti u) (hv : StrictAnti v) :
    coeff (gridExponent u v) (gridKernel (ell := ell)).det = if u = v then 1 else 0 := by
  classical
  rw [Matrix.det_apply', map_sum]
  have hsign (σ : Equiv.Perm (Fin ell)) (P : MvPowerSeries (GridIndex ell) ℂ) :
      coeff (gridExponent u v) (((sign σ : ℤ) : MvPowerSeries (GridIndex ell) ℂ) * P) =
        ((sign σ : ℤ) : ℂ) * coeff (gridExponent u v) P := by
    rw [← map_intCast (C : ℂ →+* MvPowerSeries (GridIndex ell) ℂ), coeff_C_mul]
  simp_rw [hsign, coeff_matchingProduct]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin ell))]
  · by_cases h : ∀ j, u j = v j
    · have huv := funext h
      simp [huv]
    · have huv : u ≠ v := fun e => h (congrFun e)
      simp [h, huv]
  · intro σ hσ hn
    have h : ¬ ∀ j, u (σ j) = v j := by
      intro hmatch
      apply hn
      apply Equiv.ext
      have hm : StrictMono σ := by
        intro a b hab
        by_contra! hn'
        apply (not_lt_of_ge (hu.antitone hn'))
        rw [hmatch a, hmatch b]
        exact hv hab
      exact fun j => hm.apply_eq
    rw [ite_eq_right h, mul_zero]
  · simp

end

end LiteralColoring

#print axioms LiteralColoring.coeff_matchingProduct
#print axioms LiteralColoring.coeff_gridKernel_det
```

## FallingDeterminant.lean

```lean
import VandermondeSigns
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Nat.Factorial.BigOperators

open scoped BigOperators
open Polynomial Matrix

namespace LiteralColoring

noncomputable section

private def falling (k : ℕ) : ℝ[X] :=
  ∏ i ∈ Finset.range k, (X - C (i : ℝ))

private theorem falling_monic (k : ℕ) : (falling k).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

private theorem falling_degree (k : ℕ) : (falling k).natDegree = k := by
  unfold falling
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_range]

private theorem falling_eval (u k : ℕ) :
    (falling k).eval (u : ℝ) = (u.descFactorial k : ℝ) := by
  classical
  rw [falling, eval_prod, Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  by_cases hu : k ≤ u
  · apply Finset.prod_congr rfl
    intro i hi
    have hle : i ≤ u := (Finset.mem_range.mp hi).le.trans hu
    simp [Nat.cast_sub hle]
  · have hmem : u ∈ Finset.range k := Finset.mem_range.mpr (Nat.lt_of_not_ge hu)
    rw [Finset.prod_eq_zero hmem, Finset.prod_eq_zero hmem]
    · simp
    · simp

private theorem det_eval_falling {ell : ℕ} (x : Fin ell → ℝ) :
    (of fun i j : Fin ell => (falling j.val).eval (x i)).det = (vandermonde x).det := by
  classical
  let T : Matrix (Fin ell) (Fin ell) ℝ := of fun i j => (falling j.val).coeff i.val
  have hT : T.IsUpperTriangular := by
    intro i j hij
    apply coeff_eq_zero_of_natDegree_lt
    rw [falling_degree]
    exact Fin.lt_def.mp hij
  have hdiag (i : Fin ell) : T i i = 1 := by
    change (falling i.val).coeff i.val = 1
    simpa only [falling_degree] using (falling_monic i.val).coeff_natDegree
  have hdet : T.det = 1 := by rw [det_of_isUpperTriangular hT]; simp [hdiag]
  have he : (of fun i j : Fin ell => (falling j.val).eval (x i)) = vandermonde x * T := by
    ext i j
    rw [Matrix.of_apply, Matrix.mul_apply,
      (falling j.val).eval_eq_sum_range' (n := ell) (by rw [falling_degree]; exact j.isLt)]
    change (∑ k ∈ Finset.range ell, (falling j.val).coeff k * x i ^ k) =
      ∑ k : Fin ell, x i ^ k.val * (falling j.val).coeff k.val
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => x i ^ k * (falling j.val).coeff k)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [mul_comm]
  rw [he, det_mul, hdet, mul_one]

def fallingMatrix {ell : ℕ} (u : Fin ell → ℕ) : Matrix (Fin ell) (Fin ell) ℝ :=
  of fun i j => (Nat.descFactorial (u j) (descendingOffset i) : ℝ)

theorem fallingMatrix_det {ell : ℕ} (u : Fin ell → ℕ) :
    (fallingMatrix u).det = (vandermonde (fun i => (u (Fin.rev i) : ℝ))).det := by
  let r : Equiv.Perm (Fin ell) := Fin.revPerm
  rw [← det_transpose, ← det_submatrix_equiv_self r]
  have he : (fallingMatrix u).transpose.submatrix r r =
      of (fun i j : Fin ell => (falling j.val).eval (u (Fin.rev i) : ℝ)) := by
    ext i j
    change (Nat.descFactorial (u (Fin.rev i)) (descendingOffset (Fin.rev j)) : ℝ) = _
    rw [Matrix.of_apply, falling_eval]
    congr 2
    unfold descendingOffset
    have hj := j.isLt
    change ell - 1 - (ell - (j.val + 1)) = j.val
    omega
  rw [he, det_eval_falling]

theorem fallingMatrix_det_pos {ell : ℕ} (u : Fin ell → ℕ) (hu : StrictAnti u) :
    0 < (fallingMatrix u).det := by
  classical
  rw [fallingMatrix_det, det_vandermonde]
  refine Finset.prod_pos (fun i _ => Finset.prod_pos (fun j hj => ?_))
  apply sub_pos.mpr
  exact_mod_cast hu (Fin.rev_lt_rev.mpr (Finset.mem_Ioi.mp hj))

end

end LiteralColoring

#print axioms LiteralColoring.fallingMatrix_det
#print axioms LiteralColoring.fallingMatrix_det_pos
```

## VirtualGrouping.lean

```lean
import VirtualNorm

open scoped BigOperators
open CategoryTheory

namespace LiteralColoring

noncomputable section

theorem virtual_norm_one_simples_up_to_sign {G I : Type*} [Group G] [Fintype G] [Fintype I]
    (V : I → FDRep ℂ G) (hs : ∀ i, Simple (V i)) (c : I → ℤ)
    (f : G → ℂ) (hf : f = fun h => ∑ i, (c i : ℂ) * (V i).character h)
    (hn : normalizedPairing f f = 1) :
    ∃ W : FDRep ℂ G, Simple W ∧ (f = W.character ∨ f = -W.character) := by
  classical
  let S : Setoid I :=
    ⟨fun i j => Nonempty (V i ≅ V j),
      fun i => ⟨Iso.refl _⟩,
      fun ⟨e⟩ => ⟨e.symm⟩,
      fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩
  let _ : Fintype (Quotient S) := Fintype.ofFinite _
  let q : I → Quotient S := Quotient.mk S
  let W (a : Quotient S) := V a.out
  let d (a : Quotient S) : ℤ := ∑ i with q i = a, c i
  have ho (a : Quotient S) : q a.out = a := Quotient.out_eq a
  have hV (i : I) : (W (q i)).character = (V i).character := by
    obtain ⟨e⟩ : Nonempty (W (q i) ≅ V i) := Quotient.exact (ho (q i))
    exact FDRep.char_iso e
  have hW : f = fun h => ∑ a, (d a : ℂ) * (W a).character h := by
    funext h
    rw [hf]
    change (∑ i, (c i : ℂ) * (V i).character h) = _
    have hterm (i : I) : (V i).character h = (W (q i)).character h :=
      congrFun (hV i).symm h
    simp_rw [hterm]
    symm
    unfold d
    push_cast
    simp_rw [Finset.sum_mul, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  apply virtual_norm_one_up_to_sign W (fun a => hs a.out) _ d f hW hn
  intro a b ha
  exact (ho a).symm.trans ((Quotient.sound (s := S) ha).trans (ho b))

end

end LiteralColoring

#print axioms LiteralColoring.virtual_norm_one_simples_up_to_sign
```

## AlternantDegree.lean

```lean
import FallingDeterminant
import SignedPairing
import Mathlib.Algebra.MvPolynomial.Coeff

open scoped BigOperators
open MvPolynomial Equiv.Perm

namespace LiteralColoring

noncomputable section

private theorem cyclePowerProduct_one (n ell : ℕ) :
    cyclePowerProduct n ell (1 : Equiv.Perm (Fin n)) =
      (∑ i : Fin ell, (X i : MvPolynomial (Fin ell) ℂ)) ^ n := by
  simp [cyclePowerProduct, fullCycleType, powerSum]

private theorem factorial_times_character_one {n ell : ℕ} (a : Fin ell → ℕ)
    (ha : ∑ i, a i = n) :
    (∏ i, (Nat.factorial (a i) : ℂ)) * (coloringRep a).character (1 : Equiv.Perm (Fin n)) =
      (Nat.factorial n : ℂ) := by
  classical
  rw [character_eq_cycle_coefficient, cyclePowerProduct_one, coeff_sum_X_pow_of_fintype]
  have hsum : (exponent a).sum (fun _ m => m) = n := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    exact ha
  simp only [hsum, ite_true]
  rw [Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)]
  have hspec := Nat.multinomial_spec (Finset.univ : Finset (Fin ell)) a
  rw [ha] at hspec
  exact_mod_cast hspec

private theorem signed_term_one {n ell : ℕ} (u : Fin ell → ℕ)
    (hu : ∑ i, u i = n + ∑ i : Fin ell, descendingOffset i) (σ : Equiv.Perm (Fin ell)) :
    (signedWeight u σ * (coloringRep (shiftedMargin u σ)).character (1 : Equiv.Perm (Fin n))) *
        (∏ i, (Nat.factorial (u i) : ℂ)) =
      (Nat.factorial n : ℂ) * (((sign σ : ℤ) : ℂ) *
        ∏ i, (Nat.descFactorial (u i) (descendingOffset (σ i)) : ℂ)) := by
  classical
  by_cases hs : ValidShift u σ
  · have hprod :
        (∏ i, (Nat.factorial (shiftedMargin u σ i) : ℂ)) *
          (∏ i, (Nat.descFactorial (u i) (descendingOffset (σ i)) : ℂ)) =
        ∏ i, (Nat.factorial (u i) : ℂ) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      have hle := (validShift_iff u σ).mp hs i
      have hn : shiftedMargin u σ i = u i - descendingOffset (σ i) := by
        have := shiftedMargin_add_offset u σ hs i
        omega
      rw [hn]
      exact_mod_cast Nat.factorial_mul_descFactorial hle
    have hfac := factorial_times_character_one (shiftedMargin u σ) (shiftedMargin_sum u σ hu hs)
    rw [← hprod]
    simp only [signedWeight, ite_eq_left hs]
    linear_combination
      (((sign σ : ℤ) : ℂ) * ∏ i, (Nat.descFactorial (u i) (descendingOffset (σ i)) : ℂ)) * hfac
  · have hinvalid : ¬ ∀ i, descendingOffset (σ i) ≤ u i := fun h => hs ((validShift_iff u σ).mpr h)
    push Not at hinvalid
    obtain ⟨i, hi⟩ := hinvalid
    have hz : (Nat.descFactorial (u i) (descendingOffset (σ i)) : ℂ) = 0 := by
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr hi, Nat.cast_zero]
    have hzero : (∏ j, (Nat.descFactorial (u j) (descendingOffset (σ j)) : ℂ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hz
    rw [hzero]
    simp [signedWeight, hs]

theorem signedCharacter_identity_factorial {n ell : ℕ} (u : Fin ell → ℕ)
    (hu : ∑ i, u i = n + ell * (ell - 1) / 2) :
    signedCharacter n u 1 * (∏ i, (Nat.factorial (u i) : ℂ)) =
      (Nat.factorial n : ℂ) * ((fallingMatrix u).det : ℂ) := by
  classical
  rw [signedCharacter, Finset.sum_mul]
  have hu' : ∑ i, u i = n + ∑ i : Fin ell, descendingOffset i := by rwa [offset_sum]
  simp_rw [signed_term_one u hu']
  rw [← Finset.mul_sum]
  congr 1
  have hm : Complex.ofRealHom.mapMatrix (fallingMatrix u) =
      Matrix.of (fun i j : Fin ell => (Nat.descFactorial (u j) (descendingOffset i) : ℂ)) := by
    ext i j
    simp [fallingMatrix]
  rw [← show Complex.ofRealHom ((fallingMatrix u).det) = ((fallingMatrix u).det : ℂ) from rfl,
    RingHom.map_det, hm, Matrix.det_apply']
  rfl

theorem signedCharacter_identity_pos {n ell : ℕ} (u : Fin ell → ℕ)
    (hu : StrictAnti u) (hU : ∑ i, u i = n + ell * (ell - 1) / 2) :
    0 < (signedCharacter n u 1).re := by
  classical
  have hr := congrArg Complex.re (signedCharacter_identity_factorial u hU)
  have hprod : (∏ i, (Nat.factorial (u i) : ℂ)) =
      ((∏ i, (Nat.factorial (u i) : ℝ) : ℝ) : ℂ) := by
    change _ = Complex.ofRealHom (∏ i, (Nat.factorial (u i) : ℝ))
    rw [map_prod]
    simp
  rw [hprod] at hr
  have hf : (Nat.factorial n : ℂ) = ((Nat.factorial n : ℝ) : ℂ) := by push_cast; rfl
  rw [hf] at hr
  change (signedCharacter n u 1 * _).re = (_ * _ : ℂ).re at hr
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hr
  have hpos : 0 < (Nat.factorial n : ℝ) * (fallingMatrix u).det :=
    mul_pos (by exact_mod_cast Nat.factorial_pos n) (fallingMatrix_det_pos u hu)
  have hp : 0 < ∏ i, (Nat.factorial (u i) : ℝ) :=
    Finset.prod_pos (fun i _ => by exact_mod_cast Nat.factorial_pos (u i))
  exact pos_of_mul_pos_left (hr.symm ▸ hpos) hp.le

end

end LiteralColoring

#print axioms LiteralColoring.signedCharacter_identity_factorial
#print axioms LiteralColoring.signedCharacter_identity_pos
```

## AlternantOrthogonality.lean

```lean
import VandermondeSigns
import CauchyDiagonal

open scoped BigOperators
open MvPowerSeries Equiv.Perm

namespace LiteralColoring

noncomputable section

private theorem left_exp_sum {ell : ℕ} (a : Fin ell → ℕ) :
    (∑ i, Finsupp.single (Sum.inl i : GridIndex ell) (a i)) = gridExponent a 0 := by
  classical
  ext p
  cases p with
  | inl j => simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
  | inr j => simp [Finsupp.finsetSum_apply]

private theorem right_exp_sum {ell : ℕ} (a : Fin ell → ℕ) :
    (∑ i, Finsupp.single (Sum.inr i : GridIndex ell) (a i)) = gridExponent 0 a := by
  classical
  ext p
  cases p with
  | inl j => simp [Finsupp.finsetSum_apply]
  | inr j => simp [Finsupp.finsetSum_apply, Finsupp.single_apply]

private theorem series_descending_expansion {ell : ℕ} (f : Fin ell → GridIndex ell) :
    descendingDet (fun i => X (R := ℂ) (f i)) =
      ∑ σ : Equiv.Perm (Fin ell),
        monomial (∑ i, Finsupp.single (f i) (descendingOffset (σ i))) ((sign σ : ℤ) : ℂ) := by
  classical
  rw [descendingDet, Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ hσ
  simp only [Matrix.of_apply, X_pow_eq, prod_monomial, Finset.prod_const_one]
  rw [← map_intCast (C : ℂ →+* MvPowerSeries (GridIndex ell) ℂ)]
  change monomial 0 _ * monomial _ 1 = _
  rw [monomial_mul_monomial, zero_add, mul_one]

theorem cauchy_grid_identity (ell : ℕ) :
    (gridKernel (ell := ell)).det =
      (descendingDet (fun i => X (R := ℂ) (Sum.inl i : GridIndex ell)) *
        descendingDet (fun j => X (R := ℂ) (Sum.inr j : GridIndex ell))) * gridProduct ell := by
  rw [descendingDet_mul]
  exact det_cauchy_of_inverse _ _ _ gridKernel_inverse

private theorem gridExponent_add {ell : ℕ} (a b : Fin ell → ℕ) :
    gridExponent a 0 + gridExponent 0 b = gridExponent a b := by
  ext p
  cases p <;> simp

private theorem coeff_signed_term {ell : ℕ} (u v : Fin ell → ℕ) (σ τ : Equiv.Perm (Fin ell)) :
    coeff (gridExponent u v)
      ((monomial (gridExponent (descendingOffset ∘ σ) (descendingOffset ∘ τ))
        (((sign σ : ℤ) : ℂ) * ((sign τ : ℤ) : ℂ))) * gridProduct ell) =
      signedWeight u σ * signedWeight v τ *
        (Nat.card (Contingency (shiftedMargin u σ) (shiftedMargin v τ)) : ℂ) := by
  classical
  rw [coeff_monomial_mul]
  have hle : gridExponent (descendingOffset ∘ σ) (descendingOffset ∘ τ) ≤ gridExponent u v ↔
      ValidShift u σ ∧ ValidShift v τ := by
    rw [validShift_iff, validShift_iff]
    refine ⟨fun h => ⟨fun i => h (Sum.inl i), fun j => h (Sum.inr j)⟩, ?_⟩
    rintro ⟨ha,hb⟩ p
    cases p with
    | inl i => exact ha i
    | inr j => exact hb j
  simp only [hle]
  by_cases hu : ValidShift u σ <;> by_cases hv : ValidShift v τ
  · have he : gridExponent u v - gridExponent (descendingOffset ∘ σ) (descendingOffset ∘ τ) =
        gridExponent (shiftedMargin u σ) (shiftedMargin v τ) := by
      ext p
      cases p with
      | inl i =>
        change u i - descendingOffset (σ i) = shiftedMargin u σ i
        have := shiftedMargin_add_offset u σ hu i
        omega
      | inr j =>
        change v j - descendingOffset (τ j) = shiftedMargin v τ j
        have := shiftedMargin_add_offset v τ hv j
        omega
    simp [hu, hv, he, signedWeight, coeff_gridProduct]
  · simp [hu, hv, signedWeight]
  · simp [hu, hv, signedWeight]
  · simp [hu, hv, signedWeight]

theorem coeff_gridKernel_det_eq_signedContingency {ell : ℕ} (u v : Fin ell → ℕ) :
    coeff (gridExponent u v) (gridKernel (ell := ell)).det = signedContingency u v := by
  classical
  rw [cauchy_grid_identity, series_descending_expansion, series_descending_expansion]
  unfold signedContingency
  simp_rw [left_exp_sum, right_exp_sum, Finset.sum_mul, Finset.mul_sum, map_sum,
    monomial_mul_monomial, gridExponent_add]
  simp_rw [Finset.sum_mul, map_sum]
  exact Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun τ _ => coeff_signed_term u v σ τ))

theorem signedContingency_eq_delta {ell : ℕ} (u v : Fin ell → ℕ)
    (hu : StrictAnti u) (hv : StrictAnti v) :
    signedContingency u v = if u = v then 1 else 0 := by
  rw [← coeff_gridKernel_det_eq_signedContingency, coeff_gridKernel_det u v hu hv]

theorem signedCharacter_orthogonality {n ell : ℕ} (u v : Fin ell → ℕ)
    (hu : StrictAnti u) (hv : StrictAnti v)
    (hU : ∑ i, u i = n + ell * (ell - 1) / 2)
    (hV : ∑ i, v i = n + ell * (ell - 1) / 2) :
    normalizedPairing (signedCharacter n u) (signedCharacter n v) = if u = v then 1 else 0 := by
  rw [normalizedPairing_signedCharacter u v (by rwa [offset_sum]) (by rwa [offset_sum])]
  exact signedContingency_eq_delta u v hu hv

end

end LiteralColoring

#print axioms LiteralColoring.cauchy_grid_identity
#print axioms LiteralColoring.coeff_gridKernel_det_eq_signedContingency
#print axioms LiteralColoring.signedContingency_eq_delta
#print axioms LiteralColoring.signedCharacter_orthogonality
```

## CharacterDecomposition.lean

```lean
import VirtualGrouping
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.DFinsupp

open scoped BigOperators MonoidAlgebra
open CategoryTheory Representation

namespace LiteralColoring

noncomputable section

private theorem trace_pi_action {I : Type} [Fintype I] (P : I → Type)
    [∀ i, AddCommGroup (P i)] [∀ i, Module ℂ (P i)] [∀ i, Module.Finite ℂ (P i)]
    (f : ∀ i, P i →ₗ[ℂ] P i) :
    LinearMap.trace ℂ (∀ i, P i) (LinearMap.pi fun i => (f i).comp (LinearMap.proj i)) =
      ∑ i, LinearMap.trace ℂ (P i) (f i) := by
  classical
  let b (i : I) := Module.finBasis ℂ (P i)
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basis b), Matrix.trace]
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basis_repr, Pi.basis_apply,
    LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Pi.single_eq_same]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  rw [LinearMap.trace_eq_matrix_trace ℂ (b i), Matrix.trace]
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply]

private theorem simple_of_irreducible {G : Type} [Group G] [Fintype G]
    (V : FDRep ℂ G) [Representation.IsIrreducible V.ρ] : Simple V := by
  let _ : NeZero (Nat.card G : ℂ) := ⟨by
    rw [Nat.card_eq_fintype_card]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero⟩
  rw [FDRep.simple_iff_end_is_rank_one V,
    ← LinearEquiv.finrank_eq (Representation.linHom.invariantsEquivFDRepHom V V),
    LinearEquiv.finrank_eq (Representation.invariantsEquivIntertwiningMap V.ρ V.ρ)]
  exact Representation.IsIrreducible.finrank_intertwiningMap_self (ρ := V.ρ)

theorem exists_sum_simple_characters {G : Type} [Group G] [Fintype G] (V : FDRep ℂ G) :
    ∃ (m : ℕ) (W : Fin m → FDRep ℂ G), (∀ i, Simple (W i)) ∧
      ∀ g, V.character g = ∑ i, (W i).character g := by
  classical
  let _ : NeZero (Nat.card G : ℂ) := ⟨by
    rw [Nat.card_eq_fintype_card]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero⟩
  let M := Representation.asModule V.ρ
  have hM : Module.Finite ℂ[G] M := Module.Finite.of_restrictScalars_finite ℂ _ _
  let _ := hM
  let _ : IsSemisimpleModule ℂ[G] M := inferInstance
  obtain ⟨m, S, e, hs⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp ℂ[G] M
  let _ (i : Fin m) : Module.Finite ℂ (S i) := by
    exact inferInstanceAs (Module.Finite ℂ ((S i).restrictScalars ℂ))
  let t (i : Fin m) : RestrictScalars ℂ ℂ[G] (S i) ≃ₗ[ℂ] S i :=
    { RestrictScalars.addEquiv ℂ ℂ[G] (S i) with
      map_smul' := fun c x => by
        change RestrictScalars.addEquiv ℂ ℂ[G] (S i) (c • x) =
          c • RestrictScalars.addEquiv ℂ ℂ[G] (S i) x
        rw [RestrictScalars.addEquiv_map_smul, IsScalarTower.algebraMap_smul] }
  let hP (i : Fin m) : Module.Finite ℂ (RestrictScalars ℂ ℂ[G] (S i)) := .equiv (t i).symm
  let W (i : Fin m) : FDRep ℂ G := by
    exact @FDRep.of ℂ G _ _ (RestrictScalars ℂ ℂ[G] (S i)) _
      (RestrictScalars.module ℂ ℂ[G] (S i)) (hP i)
      (Representation.ofModule (k := ℂ) (G := G) (S i))
  refine ⟨m, W, fun i => ?_, fun g => ?_⟩
  · exact @simple_of_irreducible G _ _ (W i)
      ((Representation.isSimpleModule_iff_irreducible_ofModule (G := G) (k := ℂ) (S i)).mp (hs i))
  · let E₀ : M ≃ₗ[ℂ[G]] (∀ i, S i) := e.trans DFinsupp.linearEquivFunOnFintype
    let E : V ≃ₗ[ℂ] (∀ i, RestrictScalars ℂ ℂ[G] (S i)) := (Representation.asModuleEquiv V.ρ).symm.trans
      ((E₀.restrictScalars ℂ).trans (LinearEquiv.piCongrRight fun i => (t i).symm))
    let f := LinearMap.pi (fun i => ((W i).ρ g).comp (LinearMap.proj i))
    have hconj : E.conj (V.ρ g) = f := by
      apply LinearMap.ext
      intro x
      funext i
      change (E (V.ρ g (E.symm x))) i = (W i).ρ g (x i)
      have h (y : V) : E (V.ρ g y) i = (W i).ρ g (E y i) := by
        apply (t i).injective
        change (t i) ((t i).symm (E₀ (V.ρ g y) i)) =
          (t i) ((W i).ρ g ((t i).symm (E₀ y i)))
        let z : M := (Representation.asModuleEquiv V.ρ).symm y
        have hz : (MonoidAlgebra.single g (1 : ℂ)) • z =
            (Representation.asModuleEquiv V.ρ).symm (V.ρ g y) := by
          apply (Representation.asModuleEquiv V.ρ).injective
          change (Representation.asAlgebraHom V.ρ (MonoidAlgebra.single g 1)) y = V.ρ g y
          rw [Representation.asAlgebraHom_single_one]
        change (t i) ((t i).symm (E₀ ((Representation.asModuleEquiv V.ρ).symm (V.ρ g y)) i)) = _
        rw [← hz, map_smul]
        change (t i) ((t i).symm ((MonoidAlgebra.single g (1 : ℂ)) • E₀ z i)) =
          (t i) (Representation.ofModule (k := ℂ) (G := G) (S i) g ((t i).symm (E₀ z i)))
        rw [LinearEquiv.apply_symm_apply, Representation.ofModule, MonoidAlgebra.lift_symm_apply,
          RestrictScalars.lsmul_apply_apply]
        rfl
      rw [h, E.apply_symm_apply]
    change LinearMap.trace ℂ V (V.ρ g) = ∑ i, LinearMap.trace ℂ (RestrictScalars ℂ ℂ[G] (S i)) ((W i).ρ g)
    rw [← LinearMap.trace_conj' _ E, hconj]
    exact @trace_pi_action _ _ (fun i => RestrictScalars ℂ ℂ[G] (S i)) _ (fun i => RestrictScalars.module ℂ ℂ[G] (S i)) hP (fun i => (W i).ρ g)

end

end LiteralColoring

#print axioms LiteralColoring.exists_sum_simple_characters
```

## SignedRealization.lean

```lean
import AlternantOrthogonality
import CharacterDecomposition

open scoped BigOperators
open CategoryTheory Equiv.Perm

namespace LiteralColoring

noncomputable section

def integerWeight {ell : ℕ} (u : Fin ell → ℕ) (σ : Equiv.Perm (Fin ell)) : ℤ := by
  classical
  exact if ValidShift u σ then (sign σ : ℤ) else 0

theorem integerWeight_cast {ell : ℕ} (u : Fin ell → ℕ) (σ : Equiv.Perm (Fin ell)) :
    (integerWeight u σ : ℂ) = signedWeight u σ := by
  classical
  by_cases h : ValidShift u σ <;> simp [integerWeight, signedWeight, h]

theorem virtual_norm_one_actual_up_to_sign {G I : Type} [Group G] [Fintype G] [Fintype I]
    (V : I → FDRep ℂ G) (c : I → ℤ)
    (f : G → ℂ) (hf : f = fun h => ∑ i, (c i : ℂ) * (V i).character h)
    (hn : normalizedPairing f f = 1) :
    ∃ W : FDRep ℂ G, Simple W ∧ (f = W.character ∨ f = -W.character) := by
  classical
  choose m W hs hW using fun i => exists_sum_simple_characters (V i)
  apply virtual_norm_one_simples_up_to_sign
    (fun p : Σ i, Fin (m i) => W p.1 p.2) (fun p => hs p.1 p.2) (fun p => c p.1) f _ hn
  funext h
  rw [hf]
  change (∑ i, (c i : ℂ) * (V i).character h) = _
  simp_rw [hW, Finset.mul_sum]
  rw [Fintype.sum_sigma]

theorem signedCharacter_simple_up_to_sign {n ell : ℕ} (u : Fin ell → ℕ)
    (hu : StrictAnti u) (hU : ∑ i, u i = n + ell * (ell - 1) / 2) :
    ∃ W : FDRep ℂ (Equiv.Perm (Fin n)), Simple W ∧
      (signedCharacter n u = W.character ∨ signedCharacter n u = -W.character) := by
  apply virtual_norm_one_actual_up_to_sign (fun σ => coloringRep (shiftedMargin u σ))
    (integerWeight u) (signedCharacter n u)
  · funext g
    simp only [signedCharacter, integerWeight_cast]
  · simpa using signedCharacter_orthogonality u u hu hu hU hU

theorem signedCharacter_simple_of_degree_pos {n ell : ℕ} (u : Fin ell → ℕ)
    (hu : StrictAnti u) (hU : ∑ i, u i = n + ell * (ell - 1) / 2)
    (hp : 0 < (signedCharacter n u 1).re) :
    ∃ W : FDRep ℂ (Equiv.Perm (Fin n)), Simple W ∧ signedCharacter n u = W.character := by
  obtain ⟨W, hs, h | h⟩ := signedCharacter_simple_up_to_sign u hu hU
  · exact ⟨W, hs, h⟩
  · have hv : (signedCharacter n u 1).re = -(Module.finrank ℂ W : ℝ) := by
      rw [h]
      change (-W.character 1).re = _
      rw [FDRep.char_one, Complex.neg_re, Complex.natCast_re]
    rw [hv] at hp
    have hnn : (0 : ℝ) ≤ (Module.finrank ℂ W : ℝ) := Nat.cast_nonneg _
    linarith

theorem signedCharacter_ne_of_ne {n ell : ℕ} (u v : Fin ell → ℕ) (hu : StrictAnti u)
    (hv : StrictAnti v) (hU : ∑ i, u i = n + ell * (ell - 1) / 2)
    (hV : ∑ i, v i = n + ell * (ell - 1) / 2) (hne : u ≠ v) :
    signedCharacter n u ≠ signedCharacter n v := by
  intro h
  have h₁ := signedCharacter_orthogonality u u hu hu hU hU
  have h₂ := signedCharacter_orthogonality u v hu hv hU hV
  rw [← h] at h₂
  simp at h₁
  simp only [ite_eq_right hne] at h₂
  exact one_ne_zero (h₁.symm.trans h₂)

end

end LiteralColoring

#print axioms LiteralColoring.virtual_norm_one_actual_up_to_sign
#print axioms LiteralColoring.signedCharacter_simple_up_to_sign
#print axioms LiteralColoring.signedCharacter_simple_of_degree_pos
#print axioms LiteralColoring.signedCharacter_ne_of_ne
```

## SimpleAlternantFamily.lean

```lean
import SignedRealization
import AlternantDegree

open scoped BigOperators
open CategoryTheory

namespace LiteralColoring

noncomputable section

theorem signedCharacter_realized {n ell : ℕ} (u : Fin ell → ℕ)
    (hu : StrictAnti u) (hU : ∑ i, u i = n + ell * (ell - 1) / 2) :
    ∃ W : FDRep ℂ (Equiv.Perm (Fin n)), Simple W ∧ signedCharacter n u = W.character :=
  signedCharacter_simple_of_degree_pos u hu hU (signedCharacter_identity_pos u hu hU)

theorem exists_simple_alternant_character {n ell : ℕ} (u : Fin ell → ℕ)
    (hu : StrictAnti u) (hU : ∑ i, u i = n + ell * (ell - 1) / 2) :
    ∃ W : FDRep ℂ (Equiv.Perm (Fin n)), Simple W ∧
      ∀ g, W.character g =
        (descendingVandermonde ell * cyclePowerProduct n ell g).coeff (exponent u) := by
  obtain ⟨W, hs, hc⟩ := signedCharacter_realized u hu hU
  exact ⟨W, hs, fun g => (congrFun hc g).symm.trans (signedCharacter_eq_coefficient u g)⟩

abbrev DescendingBeta (n ell : ℕ) :=
  {u : Fin ell → ℕ // StrictAnti u ∧ ∑ i, u i = n + ell * (ell - 1) / 2}

theorem exists_simple_alternant_family (n ell : ℕ) :
    ∃ W : DescendingBeta n ell → FDRep ℂ (Equiv.Perm (Fin n)),
      (∀ u, Simple (W u)) ∧
      (∀ u g, (W u).character g =
        (descendingVandermonde ell * cyclePowerProduct n ell g).coeff (exponent u.val)) ∧
      Function.Injective (fun u => (W u).character) := by
  classical
  choose W hS hW using fun u : DescendingBeta n ell =>
    signedCharacter_realized u.val u.property.1 u.property.2
  refine ⟨W, hS, fun u g => (congrFun (hW u) g).symm.trans (signedCharacter_eq_coefficient u.val g), ?_⟩
  intro u v h
  apply Subtype.ext
  by_contra hn
  exact signedCharacter_ne_of_ne u.val v.val u.property.1 v.property.1 u.property.2 v.property.2 hn
    ((hW u).trans (h.trans (hW v).symm))

end

end LiteralColoring

#print axioms LiteralColoring.signedCharacter_realized
#print axioms LiteralColoring.exists_simple_alternant_character
#print axioms LiteralColoring.exists_simple_alternant_family
#check LiteralColoring.signedCharacter_eq_coefficient
#check LiteralColoring.normalizedPairing_signedCharacter
#check LiteralColoring.signedContingency_eq_delta
#check LiteralColoring.signedCharacter_orthogonality
#check LiteralColoring.signedCharacter_identity_factorial
#check LiteralColoring.exists_simple_alternant_family
```

## BoundedAssignments.lean

```lean
import SimpleAlternantFamily
import Mathlib.Algebra.MvPolynomial.Coeff

open scoped BigOperators
open MvPolynomial Equiv.Perm

namespace LiteralColoring
noncomputable section

abbrev MovingCycle {n : ℕ} (g : Equiv.Perm (Fin n)) := ↥g.cycleFactorsFinset

def movingLength {n : ℕ} {g : Equiv.Perm (Fin n)} (j : MovingCycle g) : ℕ :=
  j.val.support.card

def assignmentMargin {n ell : ℕ} {g : Equiv.Perm (Fin n)}
    (f : MovingCycle g → Fin ell) (i : Fin ell) : ℕ :=
  ∑ j, if f j = i then movingLength j else 0

theorem movingLength_sum {n : ℕ} (g : Equiv.Perm (Fin n)) :
    ∑ j : MovingCycle g, movingLength j = g.support.card := by
  rw [← g.sum_cycleType, cycleType_def, Finset.sum_map_val]
  exact Finset.sum_attach g.cycleFactorsFinset (fun x => x.support.card)

theorem movingLength_two_le {n : ℕ} {g : Equiv.Perm (Fin n)} (j : MovingCycle g) :
    2 ≤ movingLength j := by
  apply two_le_of_mem_cycleType (σ := g)
  rw [cycleType_def, Multiset.mem_map]
  exact ⟨j.val, j.property, rfl⟩

theorem assignmentMargin_sum {n ell : ℕ} {g : Equiv.Perm (Fin n)}
    (f : MovingCycle g → Fin ell) : ∑ i, assignmentMargin f i = g.support.card := by
  classical
  unfold assignmentMargin
  rw [Finset.sum_comm]
  simp
  simpa using movingLength_sum g

theorem cyclePowerProduct_moving {n ell : ℕ} (g : Equiv.Perm (Fin n)) :
    cyclePowerProduct n ell g =
      (∑ f : MovingCycle g → Fin ell, monomial (exponent (assignmentMargin f)) 1) *
        (∑ i : Fin ell, (X i : MvPolynomial (Fin ell) ℂ)) ^ (n - g.support.card) := by
  classical
  have hp : (g.cycleType.map (powerSum ell)).prod =
      ∏ j : MovingCycle g, powerSum ell (movingLength j) := by
    rw [cycleType_def, Multiset.map_map, Finset.prod_map_val]
    exact (Finset.prod_attach _ _).symm
  rw [cyclePowerProduct, fullCycleType, Multiset.map_add, Multiset.prod_add, hp,
    Multiset.map_replicate, Multiset.prod_replicate]
  have h1 : powerSum ell 1 = ∑ i : Fin ell, (X i : MvPolynomial (Fin ell) ℂ) := by
    simp [powerSum]
  rw [h1]
  congr 1
  simp only [powerSum]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro f _
  simp_rw [X_pow_eq_monomial, ← monomial_sum_one]
  congr 2
  ext i
  simp [Finsupp.finsetSum_apply, Finsupp.single_apply, exponent, assignmentMargin]

theorem eq_one_of_support_card_eq_zero {n : ℕ} {g : Equiv.Perm (Fin n)}
    (h : g.support.card = 0) : g = 1 := by
  apply Equiv.ext
  intro i
  change g i = i
  by_contra hn
  have hm := mem_support.mpr hn
  rw [Finset.card_eq_zero.mp h] at hm
  exact Finset.notMem_empty i hm

theorem isEmpty_movingCycle_one (n : ℕ) :
    IsEmpty (MovingCycle (1 : Equiv.Perm (Fin n))) := by
  refine ⟨fun j => ?_⟩
  simpa using j.property

@[instance_reducible] def unique_empty_assignment (n ell : ℕ) :
    Unique (MovingCycle (1 : Equiv.Perm (Fin n)) → Fin ell) := by
  letI := isEmpty_movingCycle_one n
  exact ⟨⟨fun j => isEmptyElim j⟩, fun f => funext (fun j => isEmptyElim j)⟩

end
end LiteralColoring

#print axioms LiteralColoring.movingLength_sum
#print axioms LiteralColoring.movingLength_two_le
#print axioms LiteralColoring.assignmentMargin_sum
#print axioms LiteralColoring.cyclePowerProduct_moving
#print axioms LiteralColoring.eq_one_of_support_card_eq_zero
#print axioms LiteralColoring.unique_empty_assignment
```

## BoundedTrace.lean

```lean
import BoundedAssignments

open scoped BigOperators
open MvPolynomial Equiv.Perm

namespace LiteralColoring
noncomputable section

def betaVandermonde {R : Type*} [CommRing R] {ell : ℕ} (v : Fin ell → R) : R :=
  (Matrix.vandermonde (fun i => v (Fin.rev i))).det

def shiftReciprocal (a : ℤ) : ℂ :=
  if 0 ≤ a then ((a.toNat.factorial : ℕ) : ℂ)⁻¹ else 0

theorem coeff_shift_factorial {ell r : ℕ} (u a : Fin ell → ℕ)
    (hu : ∑ i, u i = r + ∑ i, a i) :
    (monomial (exponent a) (1 : ℂ) *
        (∑ i : Fin ell, (X i : MvPolynomial (Fin ell) ℂ)) ^ r).coeff (exponent u) *
        (∏ i, (Nat.factorial (u i) : ℂ)) =
      (Nat.factorial r : ℂ) * ∏ i, (Nat.descFactorial (u i) (a i) : ℂ) := by
  classical
  by_cases h : ∀ i, a i ≤ u i
  · let b := fun i => u i - a i
    have hab (i : Fin ell) : a i + b i = u i := by
      have hi := h i
      dsimp [b]
      omega
    have he : exponent u = exponent a + exponent b := by
      ext i
      simpa [exponent] using (hab i).symm
    have hsum : ∑ i, b i = r := by
      have hz := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hab i)
      rw [Finset.sum_add_distrib, hu] at hz
      omega
    conv_lhs => arg 1; rw [he, coeff_monomial_mul]
    rw [one_mul, coeff_sum_X_pow_of_fintype]
    have hsum' : (exponent b).sum (fun _ m => m) = r := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      exact hsum
    simp only [hsum', ite_true]
    rw [Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)]
    have hspec := Nat.multinomial_spec (Finset.univ : Finset (Fin ell)) b
    rw [hsum] at hspec
    have hf : (∏ i, (Nat.factorial (b i) : ℂ)) *
        (Nat.multinomial Finset.univ (exponent b) : ℂ) = (Nat.factorial r : ℂ) := by exact_mod_cast hspec
    have hp : (∏ i, (Nat.factorial (b i) : ℂ)) *
        (∏ i, (Nat.descFactorial (u i) (a i) : ℂ)) =
        ∏ i, (Nat.factorial (u i) : ℂ) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      exact_mod_cast Nat.factorial_mul_descFactorial (h i)
    rw [← hp, ← hf]
    ac_rfl
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have hz : (∏ j, (Nat.descFactorial (u j) (a j) : ℂ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Nat.descFactorial_eq_zero_iff_lt.mpr hi])
    rw [hz, mul_zero]
    suffices hc : (monomial (exponent a) (1 : ℂ) *
        (∑ j : Fin ell, (X j : MvPolynomial (Fin ell) ℂ)) ^ r).coeff (exponent u) = 0 by rw [hc, zero_mul]
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    rw [coeff_monomial]
    split_ifs with hh
    · exfalso
      have hs := congrArg (fun d : Fin ell →₀ ℕ => d i) (Finset.mem_antidiagonal.mp hp)
      have ha := congrArg (fun d : Fin ell →₀ ℕ => d i) hh
      change p.1 i + p.2 i = u i at hs
      change a i = p.1 i at ha
      omega
    · exact zero_mul _

theorem shiftReciprocal_factorial {u a : ℕ} :
    shiftReciprocal ((u : ℤ) - (a : ℤ)) * (u.factorial : ℂ) =
      (Nat.descFactorial u a : ℂ) := by
  unfold shiftReciprocal
  split_ifs with h
  · have hle : a ≤ u := by omega
    have ht : ((u : ℤ) - (a : ℤ)).toNat = u - a := by omega
    have hf : ((u - a).factorial : ℂ) * (u.descFactorial a : ℂ) = (u.factorial : ℂ) := by
      exact_mod_cast Nat.factorial_mul_descFactorial hle
    rw [ht, ← hf, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast (u - a).factorial_ne_zero), one_mul]
  · have hlt : u < a := by omega
    simp [Nat.descFactorial_eq_zero_iff_lt.mpr hlt]

theorem falling_det_as_beta {ell : ℕ} (u : Fin ell → ℕ) :
    ((fallingMatrix u).det : ℂ) = betaVandermonde (fun i => (u i : ℂ)) := by
  rw [fallingMatrix_det, betaVandermonde]
  change Complex.ofRealHom (Matrix.vandermonde _).det = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.vandermonde]

theorem signed_falling_split {ell : ℕ} (u s : Fin ell → ℕ) :
    (∑ σ : Equiv.Perm (Fin ell), ((sign σ : ℤ) : ℂ) *
        ∏ i, (Nat.descFactorial (u i) (s i + descendingOffset (σ i)) : ℂ)) =
      (∏ i, (Nat.descFactorial (u i) (s i) : ℂ)) *
        betaVandermonde (fun i => (u i : ℂ) - (s i : ℂ)) := by
  classical
  by_cases h : ∀ i, s i ≤ u i
  · let b := fun i => u i - s i
    have hb : (fun i => (u i : ℂ) - (s i : ℂ)) = fun i => (b i : ℂ) := by
      funext i
      exact (Nat.cast_sub (h i)).symm
    have hm : Complex.ofRealHom.mapMatrix (fallingMatrix b) =
        Matrix.of (fun i j : Fin ell => (Nat.descFactorial (b j) (descendingOffset i) : ℂ)) := by
      ext i j
      simp [fallingMatrix]
    rw [hb, ← falling_det_as_beta]
    change _ = _ * Complex.ofRealHom (fallingMatrix b).det
    rw [RingHom.map_det, hm, Matrix.det_apply', Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    have hterm (i : Fin ell) :
        (Nat.descFactorial (u i) (s i + descendingOffset (σ i)) : ℂ) =
          (Nat.descFactorial (b i) (descendingOffset (σ i)) : ℂ) *
            (Nat.descFactorial (u i) (s i) : ℂ) := by
      have hz := Nat.descFactorial_mul_descFactorial (n := u i)
        (Nat.le_add_right (s i) (descendingOffset (σ i)))
      rw [Nat.add_sub_cancel_left] at hz
      exact_mod_cast hz.symm
    simp only [hterm, Finset.prod_mul_distrib, Matrix.of_apply]
    ac_rfl
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have hz : (∏ j, (Nat.descFactorial (u j) (s j) : ℂ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Nat.descFactorial_eq_zero_iff_lt.mpr hi])
    rw [hz, zero_mul]
    apply Finset.sum_eq_zero
    intro σ _
    have hlt : u i < s i + descendingOffset (σ i) := by omega
    rw [Finset.prod_eq_zero (Finset.mem_univ i)
      (show (Nat.descFactorial (u i) (s i + descendingOffset (σ i)) : ℂ) = 0 by
        simp [Nat.descFactorial_eq_zero_iff_lt.mpr hlt]), mul_zero]

def evaluatedNumerator {n ell : ℕ} (g : Equiv.Perm (Fin n)) (u : Fin ell → ℕ) : ℂ :=
  ∑ f : MovingCycle g → Fin ell,
    (∏ i, (Nat.descFactorial (u i) (assignmentMargin f i) : ℂ)) *
      betaVandermonde (fun i => (u i : ℂ) - (assignmentMargin f i : ℂ))

end
end LiteralColoring
#print axioms LiteralColoring.shiftReciprocal_factorial
#print axioms LiteralColoring.coeff_shift_factorial
#print axioms LiteralColoring.signed_falling_split
```

## FiniteTraceExpansion.lean

```lean
import BoundedTrace

open scoped BigOperators
open MvPolynomial Equiv.Perm

namespace LiteralColoring
noncomputable section
set_option maxHeartbeats 40000
theorem signedCharacter_moving_factorial {n ell : ℕ} (u : DescendingBeta n ell)
    (g : Equiv.Perm (Fin n)) :
    signedCharacter n u.val g * (∏ i, (Nat.factorial (u.val i) : ℂ)) =
      ((n - g.support.card).factorial : ℂ) * evaluatedNumerator g u.val := by
  classical
  let r := n - g.support.card
  have hle : g.support.card ≤ n := by simpa using g.support.card_le_univ
  have hu : ∑ i, u.val i = n + ∑ i : Fin ell, descendingOffset i := by
    rw [offset_sum]
    exact u.property.2
  let P : MvPolynomial (Fin ell) ℂ := (∑ i : Fin ell, (X i : MvPolynomial (Fin ell) ℂ)) ^ r
  let T := fun (σ : Equiv.Perm (Fin ell)) (f : MovingCycle g → Fin ell) =>
    ((monomial (exponent (descendingOffset ∘ σ)) (((sign σ : ℤ) : ℂ)) *
      monomial (exponent (assignmentMargin f)) 1) * P).coeff (exponent u.val)
  have hExpansion : signedCharacter n u.val g = ∑ σ, ∑ f, T σ f := by
    rw [signedCharacter_eq_coefficient, cyclePowerProduct_moving, descendingVandermonde_expansion,
      Finset.sum_mul, coeff_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [← mul_assoc, Finset.mul_sum, Finset.sum_mul, coeff_sum]
  rw [hExpansion]
  let F : ℂ := ∏ i, (Nat.factorial (u.val i) : ℂ)
  have hDistrib : (∑ σ, ∑ f, T σ f) * F = ∑ σ, ∑ f, T σ f * F := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun σ _ => Finset.sum_mul _ _ _)
  rw [hDistrib, Finset.sum_comm]
  unfold evaluatedNumerator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [← signed_falling_split, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  let a : Fin ell → ℕ := fun i => assignmentMargin f i + descendingOffset (σ i)
  have he : exponent (descendingOffset ∘ σ) + exponent (assignmentMargin f) = exponent a := by
    ext i
    simp [a, exponent, Function.comp_apply, add_comm]
  have ha : ∑ i, u.val i = r + ∑ i, a i := by
    dsimp [a]
    rw [Finset.sum_add_distrib, assignmentMargin_sum, Equiv.sum_comp σ descendingOffset, hu]
    dsimp [r]
    omega
  have hfac := coeff_shift_factorial u.val a ha
  dsimp only [T]
  rw [monomial_mul_monomial, mul_one, he]
  have hc : monomial (exponent a) (((sign σ : ℤ) : ℂ)) =
      C (((sign σ : ℤ) : ℂ)) * monomial (exponent a) 1 := by
    rw [C_mul_monomial, mul_one]
  rw [hc, mul_assoc, coeff_C_mul, mul_assoc]
  change (((sign σ : ℤ) : ℂ)) *
    ((monomial (exponent a) (1 : ℂ) * P).coeff (exponent u.val) * F) = _
  rw [hfac]
  simp only [a]
  ac_rfl

end
end LiteralColoring
#print axioms LiteralColoring.signedCharacter_moving_factorial
```

## NormalizedTrace.lean

```lean
import FiniteTraceExpansion

open scoped BigOperators
open MvPolynomial Equiv.Perm

namespace LiteralColoring
noncomputable section
set_option maxHeartbeats 40000
theorem signedCharacter_moving_ratio {n ell : ℕ} (u : DescendingBeta n ell)
    (g : Equiv.Perm (Fin n)) :
    (Nat.descFactorial n g.support.card : ℂ) * signedCharacter n u.val g /
        signedCharacter n u.val 1 =
      evaluatedNumerator g u.val / betaVandermonde (fun i => (u.val i : ℂ)) := by
  classical
  have hidpos := signedCharacter_identity_pos u.val u.property.1 u.property.2
  have hid : signedCharacter n u.val 1 ≠ 0 := by
    intro h
    simp [h] at hidpos
  have hV : betaVandermonde (fun i => (u.val i : ℂ)) ≠ 0 := by
    rw [← falling_det_as_beta]
    exact_mod_cast (fallingMatrix_det_pos u.val u.property.1).ne'
  apply (div_eq_div_iff hid hV).2
  have hle : g.support.card ≤ n := by simpa using g.support.card_le_univ
  have hfac : (((n - g.support.card).factorial : ℕ) : ℂ) *
      (Nat.descFactorial n g.support.card : ℂ) = (n.factorial : ℂ) := by
    exact_mod_cast Nat.factorial_mul_descFactorial hle
  let F : ℂ := ∏ i, (Nat.factorial (u.val i) : ℂ)
  have hF : F ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast (u.val i).factorial_ne_zero)
  have hg := signedCharacter_moving_factorial u g
  change signedCharacter n u.val g * F = _ at hg
  have h1 := signedCharacter_identity_factorial u.val u.property.2
  rw [falling_det_as_beta] at h1
  change signedCharacter n u.val 1 * F = _ at h1
  apply mul_right_cancel₀ hF
  calc
    _ = ((n - g.support.card).factorial : ℂ) * evaluatedNumerator g u.val *
        ((Nat.descFactorial n g.support.card : ℂ) *
          betaVandermonde (fun i => (u.val i : ℂ))) := by
      rw [← hg]
      ac_rfl
    _ = evaluatedNumerator g u.val * ((n.factorial : ℂ) *
          betaVandermonde (fun i => (u.val i : ℂ))) := by
      rw [← hfac]
      ac_rfl
    _ = _ := by rw [← h1, mul_assoc]

theorem actualCharacter_moving_ratio {n ell : ℕ} (u : DescendingBeta n ell)
    (W : FDRep ℂ (Equiv.Perm (Fin n))) (hW : ∀ g, W.character g =
      (descendingVandermonde ell * cyclePowerProduct n ell g).coeff (exponent u.val))
    (g : Equiv.Perm (Fin n)) :
    0 < (W.character 1).re ∧
    (Nat.descFactorial n g.support.card : ℂ) * W.character g / W.character 1 =
      evaluatedNumerator g u.val / betaVandermonde (fun i => (u.val i : ℂ)) := by
  have hc (k : Equiv.Perm (Fin n)) : W.character k = signedCharacter n u.val k :=
    (hW k).trans (signedCharacter_eq_coefficient u.val k).symm
  simp only [hc]
  exact ⟨signedCharacter_identity_pos u.val u.property.1 u.property.2,
    signedCharacter_moving_ratio u g⟩

end
end LiteralColoring
#print axioms LiteralColoring.signedCharacter_moving_ratio
#print axioms LiteralColoring.actualCharacter_moving_ratio
```

## ReciprocalShift.lean

```lean
import FiniteTraceExpansion

open scoped BigOperators
open Equiv.Perm

namespace LiteralColoring
noncomputable section
set_option maxHeartbeats 40000

theorem signedCharacter_moving_reciprocals {n ell : ℕ} (u : DescendingBeta n ell)
    (g : Equiv.Perm (Fin n)) :
    signedCharacter n u.val g =
      ((n - g.support.card).factorial : ℂ) *
        ∑ f : MovingCycle g → Fin ell, ∑ σ : Equiv.Perm (Fin ell),
          ((sign σ : ℤ) : ℂ) * ∏ i,
            shiftReciprocal ((u.val i : ℤ) - (assignmentMargin f i : ℤ) -
              (descendingOffset (σ i) : ℤ)) := by
  classical
  let F : ℂ := ∏ i, (u.val i).factorial
  have hF : F ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast (u.val i).factorial_ne_zero)
  apply mul_right_cancel₀ hF
  rw [signedCharacter_moving_factorial, mul_assoc, Finset.sum_mul]
  congr 1
  unfold evaluatedNumerator
  apply Finset.sum_congr rfl
  intro f _
  rw [← signed_falling_split, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  rw [mul_assoc]
  congr 1
  unfold F
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hr : (u.val i : ℤ) - (assignmentMargin f i : ℤ) - (descendingOffset (σ i) : ℤ) =
      (u.val i : ℤ) - ((assignmentMargin f i + descendingOffset (σ i) : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hr, shiftReciprocal_factorial]

theorem evaluatedNumerator_one {n ell : ℕ} (u : Fin ell → ℕ) :
    evaluatedNumerator (1 : Equiv.Perm (Fin n)) u = betaVandermonde (fun i => (u i : ℂ)) := by
  classical
  let := isEmpty_movingCycle_one n
  let := unique_empty_assignment n ell
  have hs (f : MovingCycle (1 : Equiv.Perm (Fin n)) → Fin ell) (i : Fin ell) :
      assignmentMargin f i = 0 :=
    Finset.sum_eq_zero (fun j _ => isEmptyElim j)
  simp [evaluatedNumerator, hs]

end
end LiteralColoring

#print axioms LiteralColoring.signedCharacter_moving_reciprocals
#print axioms LiteralColoring.evaluatedNumerator_one
```

## AlternatingDivision.lean

```lean
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

open scoped BigOperators
open MvPolynomial Equiv.Perm

namespace LiteralColoring
noncomputable section

abbrev BetaPolynomial (ell : ℕ) := MvPolynomial (Fin ell) ℂ

private def collapse {ell : ℕ} (a b x : Fin ell) : Fin ell :=
  if x = a then b else x

private theorem collapse_swap {ell : ℕ} {a b : Fin ell} (hab : a ≠ b) :
    collapse a b ∘ Equiv.swap a b = collapse a b := by
  funext x
  by_cases ha : x = a
  · subst x
    simp [collapse, hab.symm]
  by_cases hb : x = b
  · subst x
    simp [collapse, hab.symm]
  · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne ha hb]

private theorem collapse_collision {ell : ℕ} {a b x y : Fin ell} (hxy : x ≠ y)
    (h : collapse a b x = collapse a b y) :
    (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
  by_cases hx : x = a <;> by_cases hy : y = a <;> simp_all [collapse, eq_comm]

private theorem dvd_sub_collapse {ell : ℕ} (a b : Fin ell) (P : BetaPolynomial ell) :
    (X a - X b) ∣ P - rename (collapse a b) P := by
  classical
  have hX (i : Fin ell) : (X a - X b : BetaPolynomial ell) ∣ X i - X (collapse a b i) := by
    by_cases hi : i = a
    · subst i
      simp [collapse]
    · simp [collapse, hi]
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    rw [map_add, show p + q - (rename (collapse a b) p + rename (collapse a b) q) =
      (p - rename (collapse a b) p) + (q - rename (collapse a b) q) by ring]
    exact dvd_add hp hq
  | mul_X p i hp =>
    rw [map_mul, rename_X,
      show p * X i - rename (collapse a b) p * X (collapse a b i) =
        (p - rename (collapse a b) p) * X i +
          rename (collapse a b) p * (X i - X (collapse a b i)) by ring]
    exact dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right (hX i) _)

private theorem collapse_zero_iff {ell : ℕ} {a b : Fin ell} (hab : a ≠ b)
    (P : BetaPolynomial ell) :
    rename (collapse a b) P = 0 ↔ (X a - X b) ∣ P := by
  constructor
  · intro h
    simpa [h] using dvd_sub_collapse a b P
  · rintro ⟨Q, rfl⟩
    simp [collapse, hab.symm]

def BetaAlternating {ell : ℕ} (P : BetaPolynomial ell) : Prop :=
  ∀ σ : Equiv.Perm (Fin ell), rename σ P = C ((sign σ : ℤ) : ℂ) * P

private theorem alternating_diagonal {ell : ℕ} (P : BetaPolynomial ell)
    (hP : BetaAlternating P) {a b : Fin ell} (hab : a ≠ b) :
    rename (collapse a b) P = 0 := by
  have ht := congrArg (rename (R := ℂ) (collapse a b)) (hP (Equiv.swap a b))
  rw [rename_rename, collapse_swap hab, map_mul, rename_C, sign_swap hab] at ht
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, map_neg, map_one,
    neg_mul, one_mul] at ht
  have hz : (2 : BetaPolynomial ell) * rename (collapse a b) P = 0 := by
    rw [two_mul, ← eq_neg_iff_add_eq_zero]
    exact ht
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

def betaPairs (ell : ℕ) : Finset (Σ _ : Fin ell, Fin ell) :=
  Finset.univ.sigma Finset.Ioi

def betaPairFactor {ell : ℕ} (p : Σ _ : Fin ell, Fin ell) : BetaPolynomial ell :=
  X (Fin.rev p.2) - X (Fin.rev p.1)

def betaDiscriminant (ell : ℕ) : BetaPolynomial ell :=
  ∏ p ∈ betaPairs ell, betaPairFactor p

private theorem betaPairs_lt {ell : ℕ} {p : Σ _ : Fin ell, Fin ell}
    (hp : p ∈ betaPairs ell) : p.1 < p.2 :=
  Finset.mem_Ioi.mp (Finset.mem_sigma.mp hp).2

private theorem betaPairFactor_ne_zero {ell : ℕ} {p : Σ _ : Fin ell, Fin ell}
    (hp : p ∈ betaPairs ell) : betaPairFactor p ≠ 0 := by
  intro hz
  exact (ne_of_gt (betaPairs_lt hp)) (Fin.rev_injective (X_injective (sub_eq_zero.mp hz)))

theorem betaDiscriminant_ne_zero (ell : ℕ) : betaDiscriminant ell ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun _ => betaPairFactor_ne_zero)

private theorem collapse_other_factor {ell : ℕ} {p q : Σ _ : Fin ell, Fin ell}
    (hp : p ∈ betaPairs ell) (hq : q ∈ betaPairs ell) (hqp : q ≠ p) :
    rename (collapse (Fin.rev p.2) (Fin.rev p.1)) (betaPairFactor q) ≠ 0 := by
  rw [betaPairFactor, map_sub, rename_X, rename_X, sub_ne_zero]
  intro he
  have hqne : Fin.rev q.2 ≠ Fin.rev q.1 :=
    fun he => (ne_of_gt (betaPairs_lt hq)) (Fin.rev_injective he)
  rcases collapse_collision hqne (X_injective he) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · apply hqp
    cases p
    cases q
    simp_all [Fin.rev_inj]
  · have hp' := betaPairs_lt hp
    have hq' := betaPairs_lt hq
    have h1' := Fin.rev_injective h1
    have h2' := Fin.rev_injective h2
    omega

theorem betaDiscriminant_dvd_of_alternating {ell : ℕ} (P : BetaPolynomial ell)
    (hP : BetaAlternating P) : betaDiscriminant ell ∣ P := by
  classical
  have hdvd (s : Finset (Σ _ : Fin ell, Fin ell)) (hs : s ⊆ betaPairs ell) :
      (∏ p ∈ s, betaPairFactor p) ∣ P := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert p s hp ih =>
      have hp' := hs (Finset.mem_insert_self p s)
      have hs' : s ⊆ betaPairs ell := fun q hq => hs (Finset.mem_insert_of_mem hq)
      obtain ⟨Q, hQ⟩ := ih hs'
      let a := Fin.rev p.2
      let b := Fin.rev p.1
      have hab : a ≠ b := fun he => (ne_of_gt (betaPairs_lt hp')) (Fin.rev_injective he)
      have hzero := alternating_diagonal P hP hab
      rw [hQ, map_mul, map_prod] at hzero
      have hprod : (∏ q ∈ s, rename (collapse a b) (betaPairFactor q)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun q hq =>
          collapse_other_factor hp' (hs' hq) (fun he => hp (he ▸ hq)))
      obtain ⟨R, hR⟩ := (collapse_zero_iff hab Q).mp ((mul_eq_zero.mp hzero).resolve_left hprod)
      refine ⟨R, ?_⟩
      rw [Finset.prod_insert hp, hQ, hR]
      change _ * (betaPairFactor p * R) = _
      ac_rfl
  exact hdvd _ (Finset.Subset.refl _)

theorem betaDiscriminant_totalDegree (ell : ℕ) :
    (betaDiscriminant ell).totalDegree = (betaPairs ell).card := by
  have h := IsHomogeneous.prod (betaPairs ell) (@betaPairFactor ell) (fun _ => 1)
    (fun p _ => (isHomogeneous_X ℂ (Fin.rev p.2)).sub
      (isHomogeneous_X ℂ (Fin.rev p.1)))
  simpa [betaDiscriminant] using h.totalDegree (betaDiscriminant_ne_zero ell)

theorem alternating_exists_symmetric_quotient {ell q : ℕ} (P : BetaPolynomial ell)
    (hP : BetaAlternating P) (hD : BetaAlternating (betaDiscriminant ell))
    (hdeg : P.totalDegree ≤ q + (betaPairs ell).card) :
    ∃ Q : BetaPolynomial ell,
      P = betaDiscriminant ell * Q ∧ (∀ σ : Equiv.Perm (Fin ell), rename σ Q = Q) ∧
        Q.totalDegree ≤ q := by
  obtain ⟨Q, hQ⟩ := betaDiscriminant_dvd_of_alternating P hP
  have hD0 := betaDiscriminant_ne_zero ell
  refine ⟨Q, hQ, ?_, ?_⟩
  · intro σ
    have hs : C (((sign σ : ℤ) : ℂ)) ≠ (0 : BetaPolynomial ell) := by
      exact C_ne_zero.mpr (by exact_mod_cast (Units.ne_zero (sign σ)))
    apply mul_left_cancel₀ (mul_ne_zero hs hD0)
    have he := hP σ
    rw [hQ, map_mul, hD σ, ← mul_assoc] at he
    exact he
  · by_cases hQ0 : Q = 0
    · simp [hQ0]
    rw [hQ, totalDegree_mul_of_isDomain hD0 hQ0, betaDiscriminant_totalDegree] at hdeg
    omega

end
end LiteralColoring

#print axioms LiteralColoring.betaDiscriminant_ne_zero
#print axioms LiteralColoring.betaDiscriminant_dvd_of_alternating
#print axioms LiteralColoring.betaDiscriminant_totalDegree
#print axioms LiteralColoring.alternating_exists_symmetric_quotient
```

## BoundedNumerator.lean

```lean
import BoundedTrace
import AlternatingDivision

open scoped BigOperators
open MvPolynomial Equiv.Perm

namespace LiteralColoring
noncomputable section
set_option maxHeartbeats 30000

theorem betaVandermonde_eq_prod {R : Type*} [CommRing R] {ell : ℕ} (v : Fin ell → R) :
    betaVandermonde v =
      ∏ p ∈ betaPairs ell, (v (Fin.rev p.2) - v (Fin.rev p.1)) := by
  rw [betaVandermonde, Matrix.det_vandermonde, betaPairs, Finset.prod_sigma]

theorem betaVandermonde_map {A B : Type*} [CommRing A] [CommRing B]
    {ell : ℕ} (φ : A →+* B) (v : Fin ell → A) :
    φ (betaVandermonde v) = betaVandermonde (fun i => φ (v i)) := by
  simp only [betaVandermonde_eq_prod, map_prod, map_sub]

theorem betaVandermonde_perm {A : Type*} [CommRing A] {ell : ℕ}
    (v : Fin ell → A) (σ : Equiv.Perm (Fin ell)) :
    betaVandermonde (v ∘ σ) = ((sign σ : ℤ) : A) * betaVandermonde v := by
  let r : Equiv.Perm (Fin ell) := Fin.revPerm
  let τ := r * σ * r⁻¹
  have ht (i : Fin ell) : Fin.rev (τ i) = σ (Fin.rev i) := by
    simp [τ, r, mul_apply]
  have hsign : sign τ = sign σ := by
    dsimp only [τ]
    rw [map_mul, map_mul, map_inv, mul_comm (sign r) (sign σ), mul_assoc, mul_inv_cancel, mul_one]
  unfold betaVandermonde
  have he : (Matrix.vandermonde (fun i => v (Fin.rev i))).submatrix τ id =
      Matrix.vandermonde (fun i => (v ∘ σ) (Fin.rev i)) := by
    ext i j
    simp [Matrix.vandermonde, ht]
  rw [← he, Matrix.det_permute, hsign]

theorem betaDiscriminant_eq_vandermonde (ell : ℕ) :
    betaDiscriminant ell = betaVandermonde (X : Fin ell → BetaPolynomial ell) := by
  rw [betaVandermonde_eq_prod]
  rfl

theorem betaDiscriminant_alternating (ell : ℕ) : BetaAlternating (betaDiscriminant ell) := by
  intro σ
  rw [betaDiscriminant_eq_vandermonde]
  change (rename σ).toRingHom (betaVandermonde X) = _
  rw [betaVandermonde_map]
  have hX : (fun i => (rename σ).toRingHom (X i : BetaPolynomial ell)) = X ∘ σ := by
    funext i
    exact rename_X σ i
  rw [hX, betaVandermonde_perm, map_intCast]

end
end LiteralColoring
#print axioms LiteralColoring.betaDiscriminant_alternating
```

## MovingNumerator.lean

```lean
import BoundedNumerator

open scoped BigOperators
open MvPolynomial Equiv.Perm

namespace LiteralColoring
noncomputable section
set_option maxHeartbeats 25000

def fallingPoly {ell : ℕ} (i : Fin ell) (k : ℕ) : BetaPolynomial ell :=
  ∏ j ∈ Finset.range k, (X i - C (j : ℂ))

theorem eval_fallingPoly {ell : ℕ} (v : Fin ell → ℕ) (i : Fin ell) (k : ℕ) :
    eval (fun i => (v i : ℂ)) (fallingPoly i k) = (Nat.descFactorial (v i) k : ℂ) := by
  induction k with
  | zero => simp [fallingPoly]
  | succ k ih =>
    have hprod : fallingPoly i (k + 1) = fallingPoly i k * (X i - C (k : ℂ)) :=
      Finset.prod_range_succ _ _
    rw [hprod, map_mul, ih, map_sub, eval_X, eval_C, Nat.descFactorial_succ, Nat.cast_mul]
    by_cases hk : k ≤ v i
    · rw [Nat.cast_sub hk, mul_comm]
    · have hlt : v i < k := by omega
      simp [Nat.descFactorial_eq_zero_iff_lt.mpr hlt]

def movingNumerator {n ell : ℕ} (g : Equiv.Perm (Fin n)) : BetaPolynomial ell :=
  ∑ f : MovingCycle g → Fin ell,
    (∏ i, fallingPoly i (assignmentMargin f i)) *
      betaVandermonde (fun i => X i - C (assignmentMargin f i : ℂ))

theorem eval_movingNumerator {n ell : ℕ} (g : Equiv.Perm (Fin n)) (v : Fin ell → ℕ) :
    eval (fun i => (v i : ℂ)) (movingNumerator g) = evaluatedNumerator g v := by
  classical
  unfold movingNumerator evaluatedNumerator
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [map_mul, map_prod, betaVandermonde_map]
  simp only [eval_fallingPoly, map_sub, eval_X, eval_C]

end
end LiteralColoring
#print axioms LiteralColoring.eval_movingNumerator
```

## MovingPolynomialQuotient.lean

```lean
import MovingNumerator

open scoped BigOperators
open MvPolynomial Equiv.Perm

namespace LiteralColoring
noncomputable section
set_option maxHeartbeats 30000

private theorem margin_transport {n ell : ℕ} {g : Equiv.Perm (Fin n)}
    (σ : Equiv.Perm (Fin ell)) (f : MovingCycle g → Fin ell) (i : Fin ell) :
    assignmentMargin (σ ∘ f) (σ i) = assignmentMargin f i := by
  simp [assignmentMargin]

theorem movingNumerator_alternating {n ell : ℕ} (g : Equiv.Perm (Fin n)) :
    BetaAlternating (movingNumerator (ell := ell) g) := by
  classical
  intro σ
  unfold movingNumerator
  rw [map_sum, Finset.mul_sum]
  apply Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl (MovingCycle g)) σ)
  intro f
  change _ = _ * ((∏ i, fallingPoly i (assignmentMargin (σ ∘ f) i)) *
    betaVandermonde (fun i => X i - C (assignmentMargin (σ ∘ f) i : ℂ)))
  have hfall : (∏ i, rename σ (fallingPoly i (assignmentMargin f i))) =
      ∏ i, fallingPoly i (assignmentMargin (σ ∘ f) i) := by
    conv_rhs => rw [← Equiv.prod_comp σ
      (fun i => fallingPoly i (assignmentMargin (σ ∘ f) i))]
    apply Finset.prod_congr rfl
    intro i _
    simp [fallingPoly, margin_transport σ f i]
  rw [map_mul, map_prod, hfall]
  change _ * (rename σ).toRingHom (betaVandermonde _) = _
  rw [betaVandermonde_map]
  have hx (i : Fin ell) : (rename σ).toRingHom (X i - C (assignmentMargin f i : ℂ)) =
      X (σ i) - C (assignmentMargin f i : ℂ) := by
    change rename σ (X i - C (assignmentMargin f i : ℂ)) = _
    rw [map_sub, rename_X, rename_C]
  simp only [hx]
  have hv : (fun i => (X (σ i) : BetaPolynomial ell) - C (assignmentMargin f i : ℂ)) =
      (fun i => X i - C (assignmentMargin (σ ∘ f) i : ℂ)) ∘ σ := by
    funext i
    simp [margin_transport]
  rw [hv, betaVandermonde_perm, map_intCast]
  ac_rfl

private theorem totalDegree_X_sub_C_le {ell : ℕ} (i : Fin ell) (c : ℂ) :
    ((X i : BetaPolynomial ell) - C c).totalDegree ≤ 1 := by
  exact (totalDegree_sub_C_le _ _).trans (totalDegree_X _).le

private theorem fallingPoly_totalDegree_le {ell : ℕ} (i : Fin ell) (k : ℕ) :
    (fallingPoly i k).totalDegree ≤ k := by
  refine (totalDegree_finsetProd _ _).trans ?_
  calc
    _ ≤ ∑ _ ∈ Finset.range k, (1 : ℕ) :=
      Finset.sum_le_sum (fun j _ => totalDegree_X_sub_C_le i j)
    _ = _ := by simp

theorem movingNumerator_degree {n ell : ℕ} (g : Equiv.Perm (Fin n)) :
    (movingNumerator (ell := ell) g).totalDegree ≤ g.support.card + (betaPairs ell).card := by
  classical
  unfold movingNumerator
  apply totalDegree_finsetSum_le
  intro f _
  apply (totalDegree_mul _ _).trans
  apply Nat.add_le_add
  · refine (totalDegree_finsetProd _ _).trans ?_
    simpa only [assignmentMargin_sum] using
      Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => fallingPoly_totalDegree_le i (assignmentMargin f i))
  · rw [betaVandermonde_eq_prod]
    refine (totalDegree_finsetProd _ _).trans ?_
    calc
      _ ≤ ∑ _ ∈ betaPairs ell, (1 : ℕ) := by
        apply Finset.sum_le_sum
        intro p _
        refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
        · exact totalDegree_X_sub_C_le _ _
        · exact totalDegree_X_sub_C_le _ _
      _ = _ := by simp

theorem movingNumerator_quotient {n ell : ℕ} (g : Equiv.Perm (Fin n)) :
    ∃ Q : BetaPolynomial ell, movingNumerator g = betaDiscriminant ell * Q ∧
      (∀ σ : Equiv.Perm (Fin ell), rename σ Q = Q) ∧ Q.totalDegree ≤ g.support.card :=
  alternating_exists_symmetric_quotient _ (movingNumerator_alternating g)
    (betaDiscriminant_alternating ell) (movingNumerator_degree g)

end
end LiteralColoring

#print axioms LiteralColoring.movingNumerator_alternating
#print axioms LiteralColoring.movingNumerator_degree
#print axioms LiteralColoring.movingNumerator_quotient
```

## WeightedMoments.lean

```lean
import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

open scoped BigOperators
open MvPolynomial

namespace LiteralColoring
noncomputable section

def BetaMomentAgreement {ell : ℕ} (q : ℕ) (a b : Fin ell → ℂ) : Prop :=
  ∀ j : ℕ, 0 < j → j ≤ q → ∑ i, a i ^ j = ∑ i, b i ^ j

theorem eval_esymm_eq_of_moments {ell q : ℕ} (a b : Fin ell → ℂ)
    (h : BetaMomentAgreement q a b) (k : ℕ) (hk : k ≤ q) :
    eval a (esymm (Fin ell) ℂ k) = eval b (esymm (Fin ell) ℂ k) := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases h0 : k = 0
    · subst k
      simp
    have hkn : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h0
    have ha := congrArg (eval a) (mul_esymm_eq_sum (Fin ell) ℂ k)
    have hb := congrArg (eval b) (mul_esymm_eq_sum (Fin ell) ℂ k)
    simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum] at ha hb
    apply mul_left_cancel₀ hkn
    rw [ha, hb]
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    have hlt := (Finset.mem_filter.mp hp).2
    have hsum : p.1 + p.2 = k := Finset.mem_antidiagonal.mp (Finset.mem_filter.mp hp).1
    have hj : 0 < p.2 := by omega
    have hjq : p.2 ≤ q := by omega
    have hiq : p.1 ≤ q := by omega
    rw [ih p.1 hlt hiq]
    congr 1
    simpa [psum] using h p.2 hj hjq

private theorem esymm_homogeneous {ell : ℕ} (k : ℕ) :
    (esymm (Fin ell) ℂ k).IsHomogeneous k := by
  classical
  unfold esymm
  apply IsHomogeneous.sum
  intro s hs
  have hs' := (Finset.mem_powersetCard.mp hs).2
  have hp := IsHomogeneous.prod s (X : Fin ell → MvPolynomial (Fin ell) ℂ)
    (fun _ => 1) (fun i _ => isHomogeneous_X ℂ i)
  simpa [hs'] using hp

private def elementaryWeight {ell : ℕ} (d : Fin ell →₀ ℕ) : ℕ :=
  ∑ i ∈ d.support, (i.val + 1) * d i

private theorem elementaryWeight_le {ell : ℕ} (d : Fin ell →₀ ℕ)
    (i : Fin ell) (hi : i ∈ d.support) : i.val + 1 ≤ elementaryWeight d := by
  have hd : 1 ≤ d i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  exact (by simpa using Nat.mul_le_mul_left (i.val + 1) hd : i.val + 1 ≤ (i.val + 1) * d i)
    |>.trans (Finset.single_le_sum (fun j _ => Nat.zero_le ((j.val + 1) * d j)) hi)

theorem eval_eq_of_symmetric_degree_moments {ell q : ℕ} (P : MvPolynomial (Fin ell) ℂ)
    (hP : P.IsSymmetric) (hdeg : P.totalDegree ≤ q) (a b : Fin ell → ℂ)
    (hm : BetaMomentAgreement q a b) : eval a P = eval b P := by
  classical
  let E := fun i : Fin ell => esymm (Fin ell) ℂ (i.val + 1)
  obtain ⟨R, hR⟩ := esymmAlgHom_surjective (σ := Fin ell) (R := ℂ) (n := ell)
    (by simp) (⟨P, hP⟩ : symmetricSubalgebra (Fin ell) ℂ)
  have hR' : aeval E R = P := by
    have h := congrArg Subtype.val hR
    rw [esymmAlgHom_apply] at h
    exact h
  let T := fun d : Fin ell →₀ ℕ => aeval E (monomial d (R.coeff d))
  have hT (d : Fin ell →₀ ℕ) : (T d).IsHomogeneous (elementaryWeight d) := by
    dsimp only [T]
    rw [aeval_monomial]
    change (C (R.coeff d) * ∏ i ∈ d.support, E i ^ d i).IsHomogeneous (elementaryWeight d)
    have hprod := IsHomogeneous.prod d.support (fun i => E i ^ d i)
      (fun i => (i.val + 1) * d i) (fun i _ => (esymm_homogeneous (i.val + 1)).pow (d i))
    simpa only [zero_add, elementaryWeight] using (isHomogeneous_C (Fin ell) (R.coeff d)).mul hprod
  have hs : P = ∑ d ∈ R.support, T d := by
    rw [← hR']
    conv_lhs => arg 2; rw [R.as_sum]
    rw [map_sum]
  have hc (k : ℕ) : homogeneousComponent k P =
      ∑ d ∈ R.support, if k = elementaryWeight d then T d else 0 := by
    rw [hs, map_sum]
    exact Finset.sum_congr rfl (fun d _ => homogeneousComponent_of_mem (hT d))
  have he (k : ℕ) (hk : k ≤ q) : eval a (homogeneousComponent k P) =
      eval b (homogeneousComponent k P) := by
    rw [hc, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro d _
    split_ifs with hw
    · dsimp only [T]
      rw [aeval_monomial]
      change eval a (C (R.coeff d) * ∏ i ∈ d.support, E i ^ d i) =
        eval b (C (R.coeff d) * ∏ i ∈ d.support, E i ^ d i)
      simp only [map_mul, eval_C, map_prod, map_pow]
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      rw [show eval a (E i) = eval b (E i) from eval_esymm_eq_of_moments a b hm _
        ((elementaryWeight_le d i hi).trans (hw ▸ hk))]
    · rfl
  calc
    eval a P = ∑ k ∈ Finset.range (P.totalDegree + 1), eval a (homogeneousComponent k P) := by
      rw [← map_sum, sum_homogeneousComponent]
    _ = ∑ k ∈ Finset.range (P.totalDegree + 1), eval b (homogeneousComponent k P) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact he k ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)).trans hdeg)
    _ = eval b P := by rw [← map_sum, sum_homogeneousComponent]

end
end LiteralColoring

#print axioms LiteralColoring.eval_esymm_eq_of_moments
#print axioms LiteralColoring.eval_eq_of_symmetric_degree_moments
```

## BoundedCharacterMoments.lean

```lean
import MovingPolynomialQuotient
import NormalizedTrace
import WeightedMoments

open scoped BigOperators
open MvPolynomial CategoryTheory

namespace LiteralColoring
noncomputable section

set_option maxHeartbeats 40000

theorem exists_symmetric_normalized_character_polynomial {n ell : ℕ}
    (g : Equiv.Perm (Fin n)) :
    ∃ Q : BetaPolynomial ell, Q.IsSymmetric ∧ Q.totalDegree ≤ g.support.card ∧
      ∀ (u : DescendingBeta n ell) (W : FDRep ℂ (Equiv.Perm (Fin n))),
        (∀ h, W.character h =
          (descendingVandermonde ell * cyclePowerProduct n ell h).coeff (exponent u.val)) →
        ((Nat.descFactorial n g.support.card : ℂ) * W.character g / W.character 1 =
          eval (fun i => (u.val i : ℂ)) Q) := by
  obtain ⟨Q, hQ, hsym, hdeg⟩ := movingNumerator_quotient (ell := ell) g
  refine ⟨Q, hsym, hdeg, ?_⟩
  intro u W hW
  rw [(actualCharacter_moving_ratio u W hW g).2, ← eval_movingNumerator, hQ, map_mul]
  have hD : eval (fun i => (u.val i : ℂ)) (betaDiscriminant ell) =
      betaVandermonde (fun i => (u.val i : ℂ)) := by
    rw [betaDiscriminant_eq_vandermonde, betaVandermonde_map]
    simp only [eval_X]
  rw [hD, mul_comm]
  apply mul_div_cancel_right₀
  rw [← falling_det_as_beta]
  exact_mod_cast (fallingMatrix_det_pos u.val u.property.1).ne'

theorem actualCharacter_eq_of_betaMoments {n ell d : ℕ}
    (u v : DescendingBeta n ell) (U V : FDRep ℂ (Equiv.Perm (Fin n)))
    (hU : ∀ h, U.character h =
      (descendingVandermonde ell * cyclePowerProduct n ell h).coeff (exponent u.val))
    (hV : ∀ h, V.character h =
      (descendingVandermonde ell * cyclePowerProduct n ell h).coeff (exponent v.val))
    (hId : U.character 1 = V.character 1)
    (hMoment : BetaMomentAgreement d (fun i => (u.val i : ℂ)) (fun i => (v.val i : ℂ)))
    (g : Equiv.Perm (Fin n)) (hg : g.support.card ≤ d) :
    U.character g = V.character g := by
  obtain ⟨Q, hsym, hdeg, hQ⟩ :=
    exists_symmetric_normalized_character_polynomial (ell := ell) g
  have hEq := eval_eq_of_symmetric_degree_moments Q hsym hdeg
    (fun i => (u.val i : ℂ)) (fun i => (v.val i : ℂ))
    (fun j hj hq => hMoment j hj (hq.trans hg))
  have hr := (hQ u U hU).trans (hEq.trans (hQ v V hV).symm)
  rw [← hId] at hr
  have hIdPos := (actualCharacter_moving_ratio u U hU g).1
  have hId0 : U.character 1 ≠ 0 := by
    intro h
    simp [h] at hIdPos
  have hgn : g.support.card ≤ n := by simpa using g.support.card_le_univ
  have hN : (Nat.descFactorial n g.support.card : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (fun hz => (Nat.not_lt_of_ge hgn) (Nat.descFactorial_eq_zero_iff_lt.mp hz))
  have hcross := (div_eq_div_iff hId0 hId0).mp hr
  exact mul_left_cancel₀ hN (mul_right_cancel₀ hId0 hcross)

theorem exists_simple_alternant_family_bounded_moments (n ell : ℕ) :
    ∃ W : DescendingBeta n ell → FDRep ℂ (Equiv.Perm (Fin n)),
      (∀ u, Simple (W u)) ∧
      (∀ u g, (W u).character g =
        (descendingVandermonde ell * cyclePowerProduct n ell g).coeff (exponent u.val)) ∧
      Function.Injective (fun u => (W u).character) ∧
      (∀ (d : ℕ) (u v : DescendingBeta n ell),
        (W u).character 1 = (W v).character 1 →
        BetaMomentAgreement d (fun i => (u.val i : ℂ)) (fun i => (v.val i : ℂ)) →
        ∀ g : Equiv.Perm (Fin n), g.support.card ≤ d → (W u).character g = (W v).character g) := by
  obtain ⟨W, hS, hC, hI⟩ := exists_simple_alternant_family n ell
  exact ⟨W, hS, hC, hI, fun d u v =>
    actualCharacter_eq_of_betaMoments u v (W u) (W v) (hC u) (hC v)⟩

end
end LiteralColoring

#print axioms LiteralColoring.exists_symmetric_normalized_character_polynomial
#print axioms LiteralColoring.actualCharacter_eq_of_betaMoments
#print axioms LiteralColoring.exists_simple_alternant_family_bounded_moments
```

## RuntimePin.lean

```lean
import Init.Meta.Defs

#eval Lean.versionString
```

## StableCharacterTests.lean

```lean
import BoundedCharacterMoments
import Mathlib.GroupTheory.Perm.ViaEmbedding

open CategoryTheory

namespace LiteralColoring

noncomputable section

/-- A finite test set may mix permutations on sets of different arities. -/
abbrev CharacterTest := Σ m : ℕ, Equiv.Perm (Fin m)

def extendCharacterTest (x : CharacterTest) {n : ℕ} (hx : x.1 ≤ n) :
    Equiv.Perm (Fin n) :=
  x.2.viaEmbedding (Fin.castLEEmb hx)

theorem support_extendCharacterTest (x : CharacterTest) {n : ℕ} (hx : x.1 ≤ n) :
    (extendCharacterTest x hx).support =
      x.2.support.map (Fin.castLEEmb hx) := by
  classical
  let e := Fin.castLEEmb hx
  ext y
  change y ∈ (x.2.viaEmbedding e).support ↔ y ∈ x.2.support.map e
  by_cases hy : y ∈ Set.range e
  · obtain ⟨i,rfl⟩ := hy
    rw [Equiv.Perm.mem_support, Equiv.Perm.viaEmbedding_apply]
    simp [e.injective.ne_iff, Equiv.Perm.mem_support]
  · have hfix := x.2.viaEmbedding_apply_of_notMem e y hy
    refine iff_of_false (by simp [Equiv.Perm.mem_support, hfix]) ?_
    intro hm
    obtain ⟨i,_,he⟩ := Finset.mem_map.mp hm
    exact hy ⟨i, he⟩

def BoundedCharacterCluster (d k n : ℕ) : Prop :=
  ∃ W : Fin k → FDRep ℂ (Equiv.Perm (Fin n)),
    (∀ i, Simple (W i)) ∧ Function.Injective (fun i => (W i).character) ∧
    ∀ i j g, g.support.card ≤ d → (W i).character g = (W j).character g

theorem boundedCharacterCluster_of_descendingBeta {d k n ell : ℕ}
    (u : Fin k → DescendingBeta n ell) (hu : Function.Injective u)
    (hdeg : ∀ i j, signedCharacter n (u i).val 1 = signedCharacter n (u j).val 1)
    (hmom : ∀ i j, BetaMomentAgreement d (fun a => ((u i).val a : ℂ))
      (fun a => ((u j).val a : ℂ))) :
    BoundedCharacterCluster d k n := by
  obtain ⟨W,hS,hC,hI,hM⟩ := exists_simple_alternant_family_bounded_moments n ell
  refine ⟨W ∘ u, fun i => hS (u i), hI.comp hu, ?_⟩
  intro i j g hg
  apply hM d (u i) (u j) _ (hmom i j) g hg
  rw [hC, hC, ← signedCharacter_eq_coefficient, ← signedCharacter_eq_coefficient]
  exact hdeg i j

theorem stable_finite_tests_of_bounded_tail {k : ℕ} (X : Finset CharacterTest)
    (hcluster : ∃ N : ℕ, ∀ n ≥ N, BoundedCharacterCluster (X.sup Sigma.fst) k n) :
    ∃ N ≥ X.sup Sigma.fst, ∀ n ≥ N,
      ∃ W : Fin k → FDRep ℂ (Equiv.Perm (Fin n)),
        (∀ i, Simple (W i)) ∧ Function.Injective (fun i => (W i).character) ∧
        ∀ i j (x : CharacterTest) (_hx : x ∈ X) (hxn : x.1 ≤ n)
          (g : Equiv.Perm (Fin n)),
          IsConj (extendCharacterTest x hxn) g → (W i).character g = (W j).character g := by
  obtain ⟨N,hN⟩ := hcluster
  refine ⟨max N (X.sup Sigma.fst), le_max_right _ _, ?_⟩
  intro n hn
  obtain ⟨W,hS,hI,hB⟩ := hN n ((le_max_left _ _).trans hn)
  refine ⟨W,hS,hI,?_⟩
  intro i j x hx hxn g hg
  obtain ⟨c,hc⟩ := hg
  have hh : (↑c : Equiv.Perm (Fin n)) * extendCharacterTest x hxn * (↑c : Equiv.Perm (Fin n))⁻¹ = g := by
    have h := congrArg (fun v : Equiv.Perm (Fin n) => v * (↑c : Equiv.Perm (Fin n))⁻¹) hc.eq
    simpa [mul_assoc] using h
  rw [← hh]
  simp only [FDRep.char_conj]
  apply hB
  rw [support_extendCharacterTest, Finset.card_map]
  exact (Finset.card_le_univ _).trans (by simpa using Finset.le_sup (f := Sigma.fst) hx)

end
end LiteralColoring

#print axioms LiteralColoring.support_extendCharacterTest
#print axioms LiteralColoring.boundedCharacterCluster_of_descendingBeta
#print axioms LiteralColoring.stable_finite_tests_of_bounded_tail
```

## BoundaryJets.lean

```lean
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.Ring

open Polynomial

namespace LiteralColoring

noncomputable section

abbrev BoundaryPoly := ℤ[X]

def occupancy (B : Finset ℕ) : BoundaryPoly := ∑ i ∈ B, X ^ i

def boundary (B : Finset ℕ) : BoundaryPoly := 1 + (X - 1) * occupancy B

def eulerOp : BoundaryPoly →ₗ[ℤ] BoundaryPoly :=
  { toFun := fun p => X * derivative p
    map_add' := by intro p q; rw [derivative_add, mul_add]
    map_smul' := by
      intro r p
      simp
      ring }

theorem eulerOp_pow (n : ℕ) : eulerOp (X ^ n) = (n : ℤ) • (X ^ n : BoundaryPoly) := by
  cases n with
  | zero => simp [eulerOp]
  | succ n =>
    change X * derivative (X ^ (n+1) : BoundaryPoly) = _
    simp only [derivative_X_pow, Nat.add_sub_cancel, smul_eq_C_mul]
    rw [pow_succ]
    ring

def eulerMoment (j : ℕ) (p : BoundaryPoly) : ℤ :=
  (eulerOp^[j] p).eval 1

theorem eulerIter_occupancy (j : ℕ) (B : Finset ℕ) :
    eulerOp^[j] (occupancy B) = ∑ i ∈ B, ((i : ℤ) ^ j) • (X ^ i : BoundaryPoly) := by
  induction j with
  | zero => simp [occupancy]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    change eulerOp (∑ i ∈ B, ((i : ℤ) ^ j) • (X ^ i : BoundaryPoly)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_smul, eulerOp_pow, smul_smul, pow_succ]

theorem eulerMoment_occupancy (j : ℕ) (B : Finset ℕ) :
    eulerMoment j (occupancy B) = ∑ i ∈ B, (i : ℤ) ^ j := by
  rw [eulerMoment, eulerIter_occupancy, Polynomial.eval_finsetSum]
  simp [smul_eq_C_mul]

theorem eulerOp_dvd {p : BoundaryPoly} {j : ℕ}
    (h : (X - 1 : BoundaryPoly) ^ (j+1) ∣ p) :
    (X - 1 : BoundaryPoly) ^ j ∣ eulerOp p := by
  obtain ⟨q,rfl⟩ := h
  change _ ∣ X * derivative (((X - 1) ^ (j+1) : BoundaryPoly) * q)
  rw [derivative_mul, derivative_pow, Nat.add_sub_cancel, pow_succ]
  refine ⟨X * (C ((j+1 : ℕ) : ℤ) * derivative (X - 1) * q + (X - 1) * derivative q), ?_⟩
  ring

theorem eulerMoment_zero_of_dvd (j : ℕ) (p : BoundaryPoly)
    (h : (X - 1 : BoundaryPoly) ^ (j+1) ∣ p) : eulerMoment j p = 0 := by
  induction j generalizing p with
  | zero =>
    obtain ⟨q,rfl⟩ := h
    simp [eulerMoment]
  | succ j ih =>
    exact ih (eulerOp p) (eulerOp_dvd h)

theorem eulerIter_sub (j : ℕ) (p q : BoundaryPoly) :
    eulerOp^[j] (p-q) = eulerOp^[j] p - eulerOp^[j] q := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [Function.iterate_succ_apply', ih]
    exact map_sub eulerOp _ _

theorem occupancy_moments_of_boundary_dvd {B C : Finset ℕ} {d : ℕ}
    (h : (X - 1 : BoundaryPoly) ^ (d+2) ∣ boundary B - boundary C) :
    ∀ j ≤ d, ∑ i ∈ B, (i : ℤ)^j = ∑ i ∈ C, (i : ℤ)^j := by
  intro j hj
  have he : boundary B - boundary C = (X - 1) * (occupancy B - occupancy C) := by
    unfold boundary
    ring
  obtain ⟨q,hq⟩ := (pow_dvd_pow (X - 1 : BoundaryPoly) (show j+2 ≤ d+2 by omega)).trans h
  rw [he, pow_succ', mul_assoc] at hq
  have hne : (X - 1 : BoundaryPoly) ≠ 0 := X_sub_C_ne_zero 1
  have hz := eulerMoment_zero_of_dvd j (occupancy B - occupancy C)
    ⟨q,mul_left_cancel₀ hne hq⟩
  simp only [eulerMoment, eulerIter_sub, eval_sub, sub_eq_zero] at hz
  exact (eulerMoment_occupancy j B).symm.trans (hz.trans (eulerMoment_occupancy j C))

def boundarySizeTwice (p : BoundaryPoly) : ℤ :=
  (derivative (derivative p)).eval 1 + (derivative p).eval 1 - ((derivative p).eval 1)^2

theorem boundarySizeTwice_mul (p q : BoundaryPoly) (hp : p.eval 1 = 1) (hq : q.eval 1 = 1) :
    boundarySizeTwice (p*q) = boundarySizeTwice p + boundarySizeTwice q := by
  simp only [boundarySizeTwice, derivative_mul, derivative_add, eval_mul, eval_add, hp, hq]
  ring

theorem boundarySizeTwice_boundary (B : Finset ℕ) :
    boundarySizeTwice (boundary B) =
      2 * (∑ i ∈ B, (i : ℤ)) - (B.card : ℤ) * ((B.card : ℤ)-1) := by
  have h0 : (occupancy B).eval 1 = B.card := by simp [occupancy, Polynomial.eval_finsetSum]
  have h1 : (derivative (occupancy B)).eval 1 = ∑ i ∈ B, (i : ℤ) := by
    have h := eulerMoment_occupancy 1 B
    change (X * derivative (occupancy B)).eval 1 = _ at h
    simpa using h
  simp [boundarySizeTwice, boundary, derivative_add, derivative_mul, derivative_sub, h0, h1]
  ring

end
end LiteralColoring

#print axioms LiteralColoring.occupancy_moments_of_boundary_dvd
#print axioms LiteralColoring.boundarySizeTwice_mul
#print axioms LiteralColoring.boundarySizeTwice_boundary
```

## ClusterPadding.lean

```lean
import Mathlib.Data.Nat.Basic

namespace LiteralColoring

/-- Two widths congruent to 1 modulo the smaller width cover a full tail,
even when both multiplicities have prescribed lower bounds. -/
theorem two_width_padding (a b u₀ v₀ t : ℕ) (ha : 0 < a)
    (hb : b % a = 1 % a)
    (ht : a * u₀ + b * v₀ + (a - 1) * b ≤ t) :
    ∃ u v : ℕ, u₀ ≤ u ∧ v₀ ≤ v ∧ a * u + b * v = t := by
  let s := t - (a * u₀ + b * v₀)
  let r := s % a
  have hr : r < a := Nat.mod_lt _ ha
  have hsb : (a - 1) * b ≤ s := by dsimp [s]; omega
  have hbr : b * r ≤ s := Nat.le_trans (Nat.mul_le_mul_left b (show r ≤ a - 1 by omega))
    (by simpa [Nat.mul_comm] using hsb)
  have hrem : (b * r) % a = r := by
    rw [Nat.mul_mod, hb, ← Nat.mul_mod]
    simp [Nat.mod_eq_of_lt hr]
  have hdiv : a * ((s - b * r) / a) = s - b * r := by
    have h₁ := Nat.mod_add_div s a
    have h₂ := Nat.mod_add_div (b * r) a
    have hrs : s % a = r := rfl
    rw [hrs] at h₁
    rw [hrem] at h₂
    have hsub : s - b * r = a * (s / a - (b * r) / a) := by
      rw [Nat.mul_sub_left_distrib]
      omega
    rw [hsub, Nat.mul_div_cancel_left _ ha]
  refine ⟨u₀ + (s - b * r) / a, v₀ + r, Nat.le_add_right _ _, Nat.le_add_right _ _, ?_⟩
  rw [Nat.mul_add, Nat.mul_add, hdiv]
  dsimp [s] at *
  omega

theorem cluster_padding_widths (D n₀ n : ℕ)
    (hn : n₀ + ((D+1) + (2*(D+1)+1)) * (D+1) + D * (2*(D+1)+1) ≤ n) :
    ∃ u v : ℕ, D < u ∧ D < v ∧ n = n₀ + (D+1)*u + (2*(D+1)+1)*v := by
  let a := D+1
  let b := 2*a+1
  have hb : b % a = 1 % a := by
    dsimp [b]
    rw [Nat.mul_comm 2 a, Nat.mul_add_mod]
  have ht : a*a + b*a + (a-1)*b ≤ n-n₀ := by
    rw [← Nat.add_mul]
    dsimp [a,b] at *
    omega
  obtain ⟨u,v,hu,hv,he⟩ := two_width_padding a b a a (n-n₀) (by dsimp [a]; omega) hb ht
  exact ⟨u,v,by omega,by omega,by dsimp [a,b] at *; omega⟩

end LiteralColoring

#print axioms LiteralColoring.two_width_padding
#print axioms LiteralColoring.cluster_padding_widths
```

## BetaHookSets.lean

```lean
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Tauto
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Factorial.BigOperators

open scoped BigOperators

namespace LiteralColoring

noncomputable section

def betaHoles (B : Finset ℕ) (b : ℕ) : Finset ℕ := Finset.range b \ B

def betaLowerBeads (B : Finset ℕ) (b : ℕ) : Finset ℕ := B.filter (· < b)

def betaHookBag (B : Finset ℕ) : Multiset ℕ :=
  B.val.bind fun b => (betaHoles B b).val.map (b - ·)

theorem betaHookBag_prod (B : Finset ℕ) :
    ((betaHookBag B).prod : ℂ) =
      ∏ b ∈ B, ∏ a ∈ betaHoles B b, ((b - a : ℕ) : ℂ) := by
  rw [betaHookBag, Multiset.prod_bind, Finset.prod_map_val, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro b _
  rw [Nat.cast_multiset_prod, Multiset.map_map, Finset.prod_map_val]
  rfl

theorem betaHookBag_prod_ne_zero (B : Finset ℕ) : ((betaHookBag B).prod : ℂ) ≠ 0 := by
  rw [betaHookBag_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro b _
  apply Finset.prod_ne_zero_iff.mpr
  intro a ha
  exact Nat.cast_ne_zero.mpr (by
    have hab := Finset.mem_range.mp (Finset.mem_sdiff.mp ha).1
    omega)

theorem factorial_eq_prod_distances (b : ℕ) :
    (b.factorial : ℂ) = ∏ a ∈ Finset.range b, ((b-a : ℕ) : ℂ) := by
  rw [Nat.factorial_eq_prod_range_add_one, Nat.cast_prod]
  apply Finset.prod_bij' (fun i _ => b-1-i) (fun a _ => b-1-a)
  · intro i hi
    have := Finset.mem_range.mp hi
    exact Finset.mem_range.mpr (by omega)
  · intro a ha
    have := Finset.mem_range.mp ha
    exact Finset.mem_range.mpr (by omega)
  · intro i hi
    have := Finset.mem_range.mp hi
    omega
  · intro a ha
    have := Finset.mem_range.mp ha
    omega
  · intro i hi
    have := Finset.mem_range.mp hi
    congr 1
    omega

theorem beta_factorial_split (B : Finset ℕ) :
    (∏ b ∈ B, (b.factorial : ℂ)) = ((betaHookBag B).prod : ℂ) *
      (∏ b ∈ B, ∏ a ∈ betaLowerBeads B b, ((b-a : ℕ) : ℂ)) := by
  rw [betaHookBag_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro b _
  rw [factorial_eq_prod_distances]
  have hsub : betaLowerBeads B b ⊆ Finset.range b := by
    intro a ha
    exact Finset.mem_range.mpr (Finset.mem_filter.mp ha).2
  have hd : Finset.range b \ betaLowerBeads B b = betaHoles B b := by
    ext a
    simp only [betaHoles, betaLowerBeads, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range]
    tauto
  rw [← hd, Finset.prod_sdiff hsub]

abbrev betaAsc (B : Finset ℕ) {ell : ℕ} (h : B.card = ell) : Fin ell ↪o ℕ :=
  B.orderEmbOfFin h

def betaDesc (B : Finset ℕ) {ell : ℕ} (h : B.card = ell) (i : Fin ell) : ℕ :=
  betaAsc B h (Fin.rev i)

theorem betaDesc_strictAnti (B : Finset ℕ) {ell : ℕ} (h : B.card = ell) :
    StrictAnti (betaDesc B h) :=
  fun _ _ hij => (betaAsc B h).strictMono (Fin.rev_lt_rev.mpr hij)

theorem betaAsc_map_univ (B : Finset ℕ) {ell : ℕ} (h : B.card = ell) :
    Finset.univ.map (betaAsc B h).toEmbedding = B := by
  ext b
  simp only [Finset.mem_map, Finset.mem_univ, true_and]
  change b ∈ Set.range (betaAsc B h) ↔ b ∈ B
  rw [B.range_orderEmbOfFin h]
  rfl

theorem betaDesc_range (B : Finset ℕ) {ell : ℕ} (h : B.card = ell) :
    Set.range (betaDesc B h) = (B : Set ℕ) := by
  rw [← B.range_orderEmbOfFin h]
  exact (Fin.revPerm.surjective.range_comp (betaAsc B h))

theorem betaDesc_sum (B : Finset ℕ) {ell : ℕ} (h : B.card = ell)
    {R : Type*} [AddCommMonoid R] (f : ℕ → R) :
    ∑ i : Fin ell, f (betaDesc B h i) = ∑ b ∈ B, f b := by
  change (∑ i : Fin ell, (f ∘ betaAsc B h) (Fin.revPerm i)) = _
  rw [Equiv.sum_comp]
  exact (Finset.sum_map Finset.univ (betaAsc B h).toEmbedding f).symm.trans
    (congrArg (fun s : Finset ℕ => ∑ b ∈ s, f b) (betaAsc_map_univ B h))

theorem betaDesc_prod (B : Finset ℕ) {ell : ℕ} (h : B.card = ell)
    {R : Type*} [CommMonoid R] (f : ℕ → R) :
    ∏ i : Fin ell, f (betaDesc B h i) = ∏ b ∈ B, f b := by
  change (∏ i : Fin ell, (f ∘ betaAsc B h) (Fin.revPerm i)) = _
  rw [Equiv.prod_comp]
  exact (Finset.prod_map Finset.univ (betaAsc B h).toEmbedding f).symm.trans
    (congrArg (fun s : Finset ℕ => ∏ b ∈ s, f b) (betaAsc_map_univ B h))

end
end LiteralColoring

#print axioms LiteralColoring.beta_factorial_split
#print axioms LiteralColoring.betaDesc_range
```

## BetaVandermondeProduct.lean

```lean
import BetaHookSets
import Mathlib.LinearAlgebra.Vandermonde

open scoped BigOperators

namespace LiteralColoring
noncomputable section

theorem vandermonde_desc (B : Finset ℕ) {ell : ℕ} (h : B.card = ell) :
    (Matrix.vandermonde (fun i => (betaDesc B h (Fin.rev i) : ℂ))).det =
      ∏ b ∈ B, ∏ a ∈ betaLowerBeads B b, ((b-a : ℕ) : ℂ) := by
  let e := betaAsc B h
  have hr (i : Fin ell) : betaDesc B h (Fin.rev i) = e i := by simp [betaDesc, e]
  rw [Matrix.det_vandermonde]
  simp only [hr]
  have hp := congrArg (fun s : Finset ℕ => ∏ b ∈ s, ∏ a ∈ betaLowerBeads B b,
    ((b-a : ℕ) : ℂ)) (betaAsc_map_univ B h)
  rw [Finset.prod_map] at hp
  rw [← hp]
  change (∏ i : Fin ell, ∏ j ∈ Finset.Ioi i, ((e j : ℂ) - e i)) = _
  rw [Finset.prod_comm' (s' := Finset.Iio) (t' := Finset.univ) (by intro i j; simp only [Finset.mem_univ, true_and, and_true, Finset.mem_Ioi, Finset.mem_Iio])]
  apply Finset.prod_congr rfl
  intro j _
  have hmap : (Finset.Iio j).map e.toEmbedding = betaLowerBeads B (e j) := by
    ext a
    constructor
    · intro ha
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp ha
      exact Finset.mem_filter.mpr ⟨B.orderEmbOfFin_mem h i, e.strictMono (Finset.mem_Iio.mp hi)⟩
    · intro ha
      obtain ⟨hb,hab⟩ := Finset.mem_filter.mp ha
      obtain ⟨i,rfl⟩ : a ∈ Set.range e := by
        rw [B.range_orderEmbOfFin h]
        exact hb
      exact Finset.mem_map.mpr ⟨i,Finset.mem_Iio.mpr (e.lt_iff_lt.mp hab),rfl⟩
  change _ = ∏ a ∈ betaLowerBeads B (e j), ((e j - a : ℕ) : ℂ)
  rw [← hmap, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro i hi
  exact (Nat.cast_sub (e.monotone (Finset.mem_Iio.mp hi).le)).symm

end
end LiteralColoring

#print axioms LiteralColoring.vandermonde_desc
```

## BetaHookDegree.lean

```lean
import BoundedCharacterMoments
import BetaVandermondeProduct

open scoped BigOperators

namespace LiteralColoring
noncomputable section

theorem signedCharacter_mul_betaHookBag (B : Finset ℕ) {n ell : ℕ} (hc : B.card = ell)
    (hs : ∑ b ∈ B, b = n + ell * (ell-1) / 2) :
    signedCharacter n (betaDesc B hc) 1 * ((betaHookBag B).prod : ℂ) = n.factorial := by
  have he := signedCharacter_identity_factorial (betaDesc B hc) ((betaDesc_sum B hc id).trans hs)
  rw [falling_det_as_beta, betaVandermonde, vandermonde_desc,
    betaDesc_prod B hc (fun b => (b.factorial : ℂ)), beta_factorial_split, ← mul_assoc] at he
  apply mul_right_cancel₀ _ he
  apply Finset.prod_ne_zero_iff.mpr
  intro b _
  apply Finset.prod_ne_zero_iff.mpr
  intro a ha
  exact Nat.cast_ne_zero.mpr (by
    have hab := (Finset.mem_filter.mp ha).2
    exact Nat.ne_of_gt (Nat.sub_pos_of_lt hab))

end
end LiteralColoring

#print axioms LiteralColoring.signedCharacter_mul_betaHookBag
```

## BetaClusterData.lean

```lean
import BetaHookSets

open scoped BigOperators

set_option maxHeartbeats 35000

namespace LiteralColoring

noncomputable section

structure ExactBetaCluster (d k n : ℕ) where
  beads : Fin k → Finset ℕ
  positive : ∀ i, 0 ∉ beads i
  distinct : Function.Injective beads
  length : ℕ
  length_eq : ∀ i, (beads i).card = length
  size_eq : ∀ i, ∑ b ∈ beads i, b = n + length * (length-1) / 2
  same_hooks : ∀ i j, betaHookBag (beads i) = betaHookBag (beads j)
  same_moments : ∀ i j q, q ≤ d → ∑ b ∈ beads i, (b : ℂ)^q = ∑ b ∈ beads j, (b : ℂ)^q

end
end LiteralColoring

```

## BetaClusterAssembly.lean

```lean
import BetaHookDegree
import BetaClusterData
import StableCharacterTests

open scoped BigOperators

set_option maxHeartbeats 35000

namespace LiteralColoring

noncomputable section

def ExactBetaCluster.indices {d k n : ℕ} (C : ExactBetaCluster d k n) :
    Fin k → DescendingBeta n C.length :=
  fun i => ⟨betaDesc (C.beads i) (C.length_eq i), betaDesc_strictAnti _ _,
    (betaDesc_sum _ _ id).trans (C.size_eq i)⟩

theorem ExactBetaCluster.indices_injective {d k n : ℕ} (C : ExactBetaCluster d k n) :
    Function.Injective C.indices := by
  intro i j h
  apply C.distinct
  have hr := congrArg (fun u : DescendingBeta n C.length => Set.range u.val) h
  change Set.range (betaDesc (C.beads i) (C.length_eq i)) =
    Set.range (betaDesc (C.beads j) (C.length_eq j)) at hr
  rw [betaDesc_range, betaDesc_range] at hr
  exact Finset.coe_injective hr

theorem ExactBetaCluster.actual {d k n : ℕ} (C : ExactBetaCluster d k n) :
    BoundedCharacterCluster d k n := by
  refine boundedCharacterCluster_of_descendingBeta C.indices C.indices_injective ?_ ?_
  · intro i j
    change signedCharacter n (betaDesc (C.beads i) (C.length_eq i)) 1 =
      signedCharacter n (betaDesc (C.beads j) (C.length_eq j)) 1
    have hi := signedCharacter_mul_betaHookBag (C.beads i) (C.length_eq i) (C.size_eq i)
    have hj := signedCharacter_mul_betaHookBag (C.beads j) (C.length_eq j) (C.size_eq j)
    rw [C.same_hooks i j] at hi
    exact mul_right_cancel₀ (betaHookBag_prod_ne_zero _) (hi.trans hj.symm)
  · intro i j q _ hq
    change (∑ a, ((betaDesc (C.beads i) (C.length_eq i) a : ℕ) : ℂ)^q) =
      ∑ a, ((betaDesc (C.beads j) (C.length_eq j) a : ℕ) : ℂ)^q
    rw [betaDesc_sum _ _ (fun b => (b : ℂ)^q), betaDesc_sum _ _ (fun b => (b : ℂ)^q)]
    exact C.same_moments i j q hq

end
end LiteralColoring

#print axioms LiteralColoring.ExactBetaCluster.indices_injective
#print axioms LiteralColoring.ExactBetaCluster.actual
```

## BoundaryShape.lean

```lean
import BoundaryJets
import Mathlib.Algebra.Polynomial.Reverse

open Polynomial
open scoped BigOperators

namespace LiteralColoring

noncomputable section

theorem coeff_occupancy (B : Finset ℕ) (i : ℕ) :
    (occupancy B).coeff i = if i ∈ B then 1 else 0 := by
  classical
  simp [occupancy, Polynomial.finsetSum_coeff, coeff_X_pow]

theorem occupancy_injective : Function.Injective occupancy := by
  intro B C h
  ext i
  have he := congrArg (fun p : BoundaryPoly => p.coeff i) h
  rw [coeff_occupancy, coeff_occupancy] at he
  by_cases hb : i ∈ B <;> by_cases hc : i ∈ C <;> simp_all

theorem boundary_injective : Function.Injective boundary := by
  intro B C h
  exact occupancy_injective (mul_left_cancel₀ (X_sub_C_ne_zero (1 : ℤ)) (add_left_cancel h))

theorem boundary_eval_one (B : Finset ℕ) : (boundary B).eval 1 = 1 := by
  simp [boundary]

theorem coeff_boundary_zero (B : Finset ℕ) (hB : 0 ∉ B) :
    (boundary B).coeff 0 = 1 := by
  simp [boundary, sub_mul, coeff_occupancy, hB]

theorem coeff_boundary_succ (B : Finset ℕ) (i : ℕ) :
    (boundary B).coeff (i+1) = (occupancy B).coeff i - (occupancy B).coeff (i+1) := by
  simp [boundary, sub_mul, coeff_one, coeff_X_mul]

theorem natDegree_boundary_le {B : Finset ℕ} {D : ℕ} (hB : ∀ b ∈ B, b < D) :
    (boundary B).natDegree ≤ D := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  cases i with
  | zero => omega
  | succ j =>
    rw [coeff_boundary_succ, coeff_occupancy, coeff_occupancy,
      ite_eq_right (fun hb => (Nat.not_lt.mpr (by omega)) (hB _ hb)),
      ite_eq_right (fun hb => (Nat.not_lt.mpr (by omega)) (hB _ hb))]
    rfl

theorem natDegree_boundary_eq {B : Finset ℕ} {D : ℕ} (hD : 0 < D)
    (hB : ∀ b ∈ B, b < D) (hTop : D - 1 ∈ B) :
    (boundary B).natDegree = D := by
  apply le_antisymm (natDegree_boundary_le hB)
  apply le_natDegree_of_ne_zero
  cases D with
  | zero => omega
  | succ j =>
    rw [coeff_boundary_succ, coeff_occupancy, coeff_occupancy]
    simp only [Nat.add_sub_cancel] at hTop
    rw [ite_eq_left hTop, ite_eq_right (fun hm => (Nat.lt_irrefl _) (hB _ hm)), sub_zero]
    exact one_ne_zero

theorem occupancy_of_binary_coefficients (p : BoundaryPoly)
    (h : ∀ i, p.coeff i = 0 ∨ p.coeff i = 1) :
    ∃ B : Finset ℕ, occupancy B = p := by
  classical
  refine ⟨p.support, ?_⟩
  ext i
  rw [coeff_occupancy]
  rcases h i with h0 | h1
  · rw [ite_eq_right (by simpa [mem_support_iff] using h0), h0]
  · rw [ite_eq_left (mem_support_iff.mpr (h1 ▸ one_ne_zero)), h1]

def mirrorBeads (B : Finset ℕ) (D : ℕ) : Finset ℕ :=
  (Finset.range D).filter fun i => D-1-i ∉ B

theorem coeff_occupancy_mirror {B : Finset ℕ} {D i : ℕ} (hi : i < D) :
    (occupancy (mirrorBeads B D)).coeff i =
      1 - (occupancy B).coeff (D-1-i) := by
  rw [coeff_occupancy, coeff_occupancy]
  by_cases h : D-1-i ∈ B <;> simp [mirrorBeads, hi, h]

theorem reflect_boundary_eq {B : Finset ℕ} {D : ℕ} (hD : 0 < D)
    (hB : ∀ b ∈ B, b < D) (hz : 0 ∉ B) (ht : D-1 ∈ B) :
    (boundary B).reflect D = boundary (mirrorBeads B D) := by
  ext i
  rw [coeff_reflect]
  have hM : ∀ b ∈ mirrorBeads B D, b < D :=
    fun _ hb => Finset.mem_range.mp (Finset.mem_filter.mp hb).1
  have hMz : 0 ∉ mirrorBeads B D := by simp [mirrorBeads, ht]
  have hMt : D-1 ∈ mirrorBeads B D := by
    simp [mirrorBeads, Nat.sub_lt hD (by decide : 0 < 1), hz]
  by_cases hle : i ≤ D
  · rw [revAt_le hle]
    by_cases h0 : i = 0
    · subst i
      rw [Nat.sub_zero, coeff_boundary_zero _ hMz]
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hD)
      change j ∈ B at ht
      rw [coeff_boundary_succ, coeff_occupancy, coeff_occupancy, ite_eq_left ht,
        ite_eq_right (fun hm => (Nat.lt_irrefl _) (hB _ hm)), sub_zero]
    by_cases htop : i = D
    · subst i
      rw [Nat.sub_self, coeff_boundary_zero _ hz]
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hD)
      change j ∈ mirrorBeads B j.succ at hMt
      rw [coeff_boundary_succ, coeff_occupancy, coeff_occupancy, ite_eq_left hMt,
        ite_eq_right (fun hm => (Nat.lt_irrefl _) (hM _ hm)), sub_zero]
    have hi : i < D := by omega
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
    have hs : D - (j+1) = (D-1-(j+1))+1 := by omega
    rw [hs, coeff_boundary_succ, coeff_boundary_succ, coeff_occupancy_mirror (by omega : j < D),
      coeff_occupancy_mirror hi]
    have hj : D-1-j = D-(j+1) := by omega
    change (occupancy B).coeff (D-1-(j+1)) - (occupancy B).coeff (D-1-(j+1)+1) =
      1 - (occupancy B).coeff (D-1-j) - (1 - (occupancy B).coeff (D-1-(j+1)))
    rw [← hs, hj]
    ring
  · have hi : D < i := by omega
    rw [revAt_eq_self_of_lt hi]
    rw [coeff_eq_zero_of_natDegree_lt ((natDegree_boundary_le hB).trans_lt hi),
      coeff_eq_zero_of_natDegree_lt ((natDegree_boundary_le hM).trans_lt hi)]

end
end LiteralColoring

#print axioms LiteralColoring.boundary_injective
#print axioms LiteralColoring.occupancy_of_binary_coefficients
#print axioms LiteralColoring.reflect_boundary_eq
```

## BoundaryProuhet.lean

```lean
import BoundaryShape
import Mathlib.Algebra.Ring.GeomSum

open Polynomial

namespace LiteralColoring

noncomputable section

def binaryProuhet : ℕ → BoundaryPoly
  | 0 => 1
  | r+1 => binaryProuhet r * (1 - X ^ (2^r))

theorem binaryProuhet_degree_le (r : ℕ) : (binaryProuhet r).natDegree ≤ 2^r-1 := by
  induction r with
  | zero => simp [binaryProuhet]
  | succ r ih =>
    have hpos : 0 < (2:ℕ)^r := Nat.two_pow_pos _
    have hdeg : (1 - (X:BoundaryPoly) ^ (2^r)).natDegree ≤ 2^r := by
      exact (natDegree_sub_le _ _).trans (max_le (by simp) (by rw [natDegree_X_pow]))
    have hp := (natDegree_mul_le).trans (Nat.add_le_add ih hdeg)
    change (binaryProuhet r * (1 - X ^ (2^r))).natDegree ≤ _ 
    rw [pow_succ]
    omega

theorem binaryProuhet_coeff_sign (r i : ℕ) (hi : i < 2^r) :
    (binaryProuhet r).coeff i = 1 ∨ (binaryProuhet r).coeff i = -1 := by
  induction r generalizing i with
  | zero =>
    have : i = 0 := by simpa using hi
    simp [binaryProuhet, this]
  | succ r ih =>
    rw [binaryProuhet]
    rw [mul_sub, mul_one, coeff_sub]
    by_cases hlo : i < 2^r
    · rw [coeff_mul_X_pow', ite_eq_right (by omega : ¬ 2^r ≤ i), sub_zero]
      exact ih i hlo
    · have hzero : (binaryProuhet r).coeff i = 0 :=
        coeff_eq_zero_of_natDegree_lt (by have := binaryProuhet_degree_le r; omega)
      rw [coeff_mul_X_pow', ite_eq_left (by omega : 2^r ≤ i), hzero, zero_sub]
      rw [pow_succ] at hi
      rcases ih (i-2^r) (by omega) with h | h <;> simp [h]

theorem binaryProuhet_one_dvd (r : ℕ) :
    (X - 1 : BoundaryPoly)^r ∣ binaryProuhet r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ]
    refine mul_dvd_mul ih ?_
    apply dvd_neg.mp
    simpa using sub_dvd_pow_sub_pow (X : BoundaryPoly) 1 (2^r)

theorem binaryProuhet_reflect (r : ℕ) :
    (binaryProuhet r).reflect (2^r-1) = C ((-1 : ℤ)^r) * binaryProuhet r := by
  induction r with
  | zero => simp [binaryProuhet]
  | succ r ih =>
    have hpos : 0 < (2:ℕ)^r := Nat.two_pow_pos _
    have hs : (2:ℕ)^(r+1)-1 = (2^r-1)+2^r := by rw [pow_succ]; omega
    have hdeg : (1 - (X:BoundaryPoly) ^ (2^r)).natDegree ≤ 2^r :=
      (natDegree_sub_le _ _).trans (max_le (by simp) (by rw [natDegree_X_pow]))
    have href : (1 - (X:BoundaryPoly) ^ (2^r)).reflect (2^r) = -(1-X^(2^r)) := by
      rw [reflect_sub, reflect_one, reflect_monomial, revAt_le (le_refl _), Nat.sub_self, pow_zero]
      ring
    rw [binaryProuhet, hs, reflect_mul _ _ (binaryProuhet_degree_le r) hdeg, ih, href,
      pow_succ, C_mul, C_neg, C_1]
    ring

theorem binaryProuhet_even_symm (s i : ℕ) (hi : i < 2^(2*s)) :
    (binaryProuhet (2*s)).coeff (2^(2*s)-1-i) = (binaryProuhet (2*s)).coeff i := by
  have h := congrArg (fun p : BoundaryPoly => p.coeff i) (binaryProuhet_reflect (2*s))
  rw [coeff_reflect, revAt_le (by omega : i ≤ 2^(2*s)-1)] at h
  have he : (-1 : ℤ)^(2*s) = 1 := by rw [pow_mul]; norm_num
  simpa only [he, C_1, one_mul] using h

end
end LiteralColoring

#print axioms LiteralColoring.binaryProuhet_coeff_sign
#print axioms LiteralColoring.binaryProuhet_one_dvd
#print axioms LiteralColoring.binaryProuhet_even_symm
```

## BoundarySeeds.lean

```lean
import BoundaryProuhet

open Polynomial

namespace LiteralColoring
noncomputable section

def seedLength (s : ℕ) : ℕ := 2^(2*s)

def seedBeads (s : ℕ) : Finset ℕ :=
  insert (seedLength s+1)
    ((Finset.range (seedLength s+1)).filter
      (fun i => 0 < i ∧ (binaryProuhet (2*s)).coeff (i-1) = 1))

theorem seedBeads_zero (s : ℕ) : 0 ∉ seedBeads s := by
  simp [seedBeads]

theorem seedBeads_top (s : ℕ) : seedLength s + 1 ∈ seedBeads s := by
  simp [seedBeads]

theorem seedBeads_lt (s b : ℕ) (hb : b ∈ seedBeads s) : b < seedLength s + 2 := by
  rcases Finset.mem_insert.mp hb with h | h
  · omega
  · have := Finset.mem_range.mp (Finset.mem_filter.mp h).1
    omega

theorem coeff_seed_interior (s i : ℕ) (hi : i < seedLength s) :
    (occupancy (seedBeads s)).coeff (i+1) =
      if (binaryProuhet (2*s)).coeff i = 1 then 1 else 0 := by
  rw [coeff_occupancy]
  have hn : i ≠ seedLength s := by omega
  have hl : i+1 < seedLength s+1 := by omega
  simp [seedBeads, hn, hl]

theorem seed_occupancy_difference (s : ℕ) :
    occupancy (seedBeads s) - occupancy (mirrorBeads (seedBeads s) (seedLength s+2)) =
      X * binaryProuhet (2*s) := by
  let L := seedLength s
  have ht := seedBeads_top s
  have hz := seedBeads_zero s
  ext i
  rw [coeff_sub]
  cases i with
  | zero =>
    rw [coeff_X_mul_zero, coeff_occupancy_mirror (by omega : 0 < L+2)]
    change (occupancy (seedBeads s)).coeff 0 - (1 - (occupancy (seedBeads s)).coeff (L+1)) = 0
    rw [coeff_occupancy, coeff_occupancy, ite_eq_right hz, ite_eq_left ht]
    norm_num
  | succ i =>
    rw [coeff_X_mul]
    by_cases hi : i < L
    · rw [coeff_seed_interior s i hi, coeff_occupancy_mirror (by omega : i+1 < L+2)]
      have ha : L+2-1-(i+1) = (L-1-i)+1 := by omega
      rw [ha, coeff_seed_interior s (L-1-i) (by omega)]
      have hs := binaryProuhet_even_symm s i hi
      change (binaryProuhet (2*s)).coeff (L-1-i) = _ at hs
      rw [hs]
      rcases binaryProuhet_coeff_sign (2*s) i hi with h | h <;> rw [h] <;> norm_num
    · have hq : (binaryProuhet (2*s)).coeff i = 0 :=
        coeff_eq_zero_of_natDegree_lt (by
          have hd : (binaryProuhet (2*s)).natDegree ≤ L-1 := binaryProuhet_degree_le _
          have hL : 0 < L := Nat.two_pow_pos _
          omega)
      rw [hq]
      by_cases htop : i = L
      · subst i
        rw [coeff_occupancy_mirror (by omega : L+1 < L+2)]
        have h : L+2-1-(L+1) = 0 := by omega
        rw [h, coeff_occupancy, coeff_occupancy, ite_eq_left ht, ite_eq_right hz]
        norm_num
      · rw [coeff_occupancy, coeff_occupancy,
          ite_eq_right (fun hm => by have := seedBeads_lt s _ hm; omega),
          ite_eq_right (fun hm => by have := Finset.mem_range.mp (Finset.mem_filter.mp hm).1; omega), sub_self]

theorem seed_boundary_difference (s : ℕ) :
    boundary (seedBeads s) - (boundary (seedBeads s)).reflect (seedLength s+2) =
      (X-1)*X*binaryProuhet (2*s) := by
  rw [reflect_boundary_eq (by omega) (seedBeads_lt s) (seedBeads_zero s) (seedBeads_top s)]
  calc
    _ = (X-1)*(occupancy (seedBeads s) - occupancy (mirrorBeads (seedBeads s) (seedLength s+2))) := by
      simp only [boundary]
      ring
    _ = _ := by rw [seed_occupancy_difference, mul_assoc]

theorem seed_boundary_pair (s : ℕ) :
    let D := seedLength s+2
    let F := boundary (seedBeads s)
    let R := F.reflect D
    (∃ B, 0 ∉ B ∧ R = boundary B) ∧
      F.natDegree = D ∧ R.natDegree = D ∧ F ≠ R ∧
      (X-1 : BoundaryPoly)^(2*s+1) ∣ F-R ∧
      F * F.reflect D = R * R.reflect D := by
  dsimp
  let D := seedLength s + 2
  have hB := seedBeads_lt s
  have ht := seedBeads_top s
  have hz := seedBeads_zero s
  have hr := reflect_boundary_eq (by omega : 0 < D) hB hz ht
  have hM : ∀ b ∈ mirrorBeads (seedBeads s) D, b < D :=
    fun _ hb => Finset.mem_range.mp (Finset.mem_filter.mp hb).1
  have hMt : D-1 ∈ mirrorBeads (seedBeads s) D := by
    simp [mirrorBeads, show D-1 < D by omega, hz]
  have htop : D-1 ∈ seedBeads s := ht
  refine ⟨⟨mirrorBeads (seedBeads s) D, by simp [mirrorBeads, htop], hr⟩,
    natDegree_boundary_eq (by omega) hB ht, hr ▸ natDegree_boundary_eq (by omega) hM hMt, ?_, ?_, ?_⟩
  · intro he
    have hp := seed_boundary_difference s
    have hz' := calc
      (X-1)*X*binaryProuhet (2*s) = boundary (seedBeads s) - (boundary (seedBeads s)).reflect (seedLength s+2) := hp.symm
      _ = 0 := sub_eq_zero.mpr he
    have hq : binaryProuhet (2*s) ≠ 0 := by
      intro h0
      rcases binaryProuhet_coeff_sign (2*s) 0 (Nat.two_pow_pos _) with h | h <;> simp [h0] at h
    exact (mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero (1 : ℤ)) X_ne_zero) hq) hz'
  · rw [seed_boundary_difference, pow_succ, mul_comm ((X-1 : BoundaryPoly)^(2*s)), mul_assoc]
    exact mul_dvd_mul_left _ ((binaryProuhet_one_dvd (2*s)).trans (dvd_mul_left _ _))
  · rw [reflect_reflect, mul_comm]

end
end LiteralColoring

#print axioms LiteralColoring.seed_boundary_pair
```

## BetaHookCounts.lean

```lean
import BetaHookSets

open scoped BigOperators

namespace LiteralColoring
noncomputable section

def betaTail (B : Finset ℕ) (h : ℕ) : ℤ := ∑ b ∈ B, if h ≤ b then 1 else 0

def beadDisplacementPairs (B : Finset ℕ) (h : ℕ) : ℤ :=
  ∑ b ∈ B, ∑ c ∈ B, if c+h = b then 1 else 0

theorem betaHookCount_eq_tail_sub_pairs (B : Finset ℕ) {h : ℕ} (hh : 0 < h) :
    ((betaHookBag B).count h : ℤ) = betaTail B h - beadDisplacementPairs B h := by
  classical
  rw [betaHookBag, Multiset.count_bind, Finset.sum_map_val, Nat.cast_sum, betaTail, beadDisplacementPairs,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [Multiset.count_map]
  simp only [eq_comm (a := h)]
  change (((betaHoles B b).filter (fun a => b-a = h)).card : ℤ) = _
  by_cases hb : h ≤ b
  · have he (a : ℕ) (ha : a < b) : b-a = h ↔ a = b-h := by omega
    have hB : (betaHoles B b).filter (fun a => b-a = h) =
        if b-h ∈ B then ∅ else {b-h} := by
      ext a
      by_cases hm : b-h ∈ B <;>
        simp only [ite_eq_left, ite_eq_right, hm, not_false_eq_true,
          Finset.mem_filter, betaHoles, Finset.mem_sdiff, Finset.mem_range,
          Finset.notMem_empty, Finset.mem_singleton] <;>
        constructor
      · rintro ⟨⟨ha,hna⟩,hd⟩
        exact hna ((he a ha).mp hd ▸ hm)
      · simp
      · rintro ⟨⟨ha,_⟩,hd⟩
        exact (he a ha).mp hd
      · rintro rfl
        exact ⟨⟨by omega,hm⟩,by omega⟩
    have hsum : (∑ c ∈ B, if c+h = b then (1:ℤ) else 0) =
        if b-h ∈ B then 1 else 0 := by
      have hiff (c : ℕ) : c+h = b ↔ c = b-h := by omega
      simp [hiff]
    rw [hB, hsum, ite_eq_left hb]
    by_cases hm : b-h ∈ B <;> simp [hm]
  · have hB : (betaHoles B b).filter (fun a => b-a = h) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      have := (Finset.mem_filter.mp ha).2
      omega
    rw [hB, Finset.card_empty, Nat.cast_zero, ite_eq_right hb]
    have hs : (∑ c ∈ B, if c+h = b then (1:ℤ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro c _
      exact ite_eq_right (by omega)
    rw [hs, sub_self]

theorem betaTail_sub_succ (B : Finset ℕ) (h : ℕ) :
    betaTail B h - betaTail B (h+1) = if h ∈ B then 1 else 0 := by
  rw [betaTail, betaTail, ← Finset.sum_sub_distrib]
  have he (b : ℕ) : ((if h ≤ b then 1 else 0) : ℤ) - (if h+1 ≤ b then 1 else 0) =
      if b = h then 1 else 0 := by
    by_cases hh : b = h <;> by_cases hl : h+1 ≤ b <;>
      simp [hh, hl, show h ≤ b ↔ b = h ∨ h+1 ≤ b by omega]
  simp [he]

theorem betaHook_count_zero (B : Finset ℕ) : (betaHookBag B).count 0 = 0 := by
  rw [Multiset.count_eq_zero]
  intro h
  obtain ⟨b,_,hb⟩ := Multiset.mem_bind.mp h
  obtain ⟨a,ha,he⟩ := Multiset.mem_map.mp hb
  have hlt := Finset.mem_range.mp (Finset.mem_sdiff.mp (show a ∈ betaHoles B b from ha)).1
  omega

theorem betaHook_count_eq_zero_of_ge {B : Finset ℕ} {D h : ℕ}
    (hB : ∀ b ∈ B, b < D) (hh : D ≤ h) : (betaHookBag B).count h = 0 := by
  rw [Multiset.count_eq_zero]
  intro hmem
  obtain ⟨b,hb,hbm⟩ := Multiset.mem_bind.mp hmem
  obtain ⟨a,_,he⟩ := Multiset.mem_map.mp hbm
  have := hB b hb
  omega

end
end LiteralColoring

#print axioms LiteralColoring.betaHookCount_eq_tail_sub_pairs
#print axioms LiteralColoring.betaTail_sub_succ
```

## BoundaryHooks.lean

```lean
import BoundaryShape
import BetaHookCounts

open Polynomial
open scoped BigOperators

namespace LiteralColoring
noncomputable section

theorem natDegree_occupancy_le {B : Finset ℕ} {D : ℕ} (hB : ∀ b ∈ B, b < D) :
    (occupancy B).natDegree ≤ D-1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [coeff_occupancy, ite_eq_right (fun hm => by have := hB _ hm; omega)]

theorem reflect_occupancy_eq_sum {B : Finset ℕ} {D : ℕ} (hB : ∀ b ∈ B, b < D) :
    (occupancy B).reflect (D-1) = ∑ b ∈ B, (X : BoundaryPoly)^(D-1-b) := by
  classical
  unfold occupancy
  induction B using Finset.induction_on with
  | empty => simp
  | insert b B hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, reflect_add,
      ih (fun c hc => hB c (Finset.mem_insert_of_mem hc)),
      reflect_monomial, revAt_le (by have := hB b (Finset.mem_insert_self _ _); omega)]

theorem reflect_boundary_expand {B : Finset ℕ} {D : ℕ}
    (hD : 0 < D) (hB : ∀ b ∈ B, b < D) :
    (boundary B).reflect D = X ^ D - (X-1) * (occupancy B).reflect (D-1) := by
  have hstep : 1 + (D-1) = D := by omega
  have hone : (X-1 : BoundaryPoly).natDegree ≤ 1 := by
    exact (natDegree_sub_le _ _).trans (by simp)
  have href : (X-1 : BoundaryPoly).reflect 1 = -(X-1) := by
    rw [reflect_sub, reflect_one, show (X:BoundaryPoly) = X^1 by simp,
      reflect_monomial, revAt_le (le_refl 1)]
    norm_num
  rw [boundary, reflect_add, reflect_one]
  conv_lhs => rhs; rw [← hstep, reflect_mul _ _ hone (natDegree_occupancy_le hB), href]
  ring

def boundaryCorr (B : Finset ℕ) (D : ℕ) : BoundaryPoly :=
  boundary B * (boundary B).reflect D

def boundaryCorrQuot (B : Finset ℕ) (D : ℕ) : BoundaryPoly :=
  X^D * occupancy B - (occupancy B).reflect (D-1) -
    (X-1) * (occupancy B * (occupancy B).reflect (D-1))

theorem boundaryCorr_expand {B : Finset ℕ} {D : ℕ} (hD : 0 < D)
    (hB : ∀ b ∈ B, b < D) :
    boundaryCorr B D = X^D + (X-1) * boundaryCorrQuot B D := by
  rw [boundaryCorr, reflect_boundary_expand hD hB, boundary, boundaryCorrQuot]
  ring

theorem coeff_beadCorrelation {B : Finset ℕ} {D : ℕ} (hB : ∀ b ∈ B, b < D) (h : ℕ) :
    (occupancy B * (occupancy B).reflect (D-1)).coeff (D-1+h) = beadDisplacementPairs B h := by
  classical
  rw [reflect_occupancy_eq_sum hB, occupancy, Finset.sum_mul, beadDisplacementPairs, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro c hc
  rw [← pow_add, coeff_X_pow]
  have he : D-1+h = b+(D-1-c) ↔ c+h = b := by
    have := hB b hb
    have := hB c hc
    omega
  simp only [he]

theorem coeff_boundaryCorrQuot {B : Finset ℕ} {D h : ℕ} (hD : 0 < D) (hh : 0 < h)
    (hB : ∀ b ∈ B, b < D) :
    (boundaryCorrQuot B D).coeff (D+h) =
      ((betaHookBag B).count h : ℤ) - ((betaHookBag B).count (h+1) : ℤ) := by
  have hmul : (X^D * occupancy B).coeff (D+h) = (occupancy B).coeff h := by
    rw [mul_comm, Nat.add_comm, coeff_mul_X_pow]
  rw [boundaryCorrQuot, coeff_sub, coeff_sub, hmul,
    coeff_reflect, revAt_eq_self_of_lt (by omega : D-1 < D+h), coeff_occupancy B (D+h),
    ite_eq_right (fun hm => by have := hB _ hm; omega), sub_zero, sub_mul, one_mul, coeff_sub]
  have he₁ : D+h = (D-1+h)+1 := by omega
  have he₂ : D+h = D-1+(h+1) := by omega
  have hx (p : BoundaryPoly) : (X*p).coeff (D+h) = p.coeff (D-1+h) := by
    rw [he₁, coeff_X_mul]
  rw [hx, coeff_beadCorrelation hB h]
  have hy := coeff_beadCorrelation hB (h+1)
  rw [← he₂] at hy
  rw [hy, betaHookCount_eq_tail_sub_pairs _ hh,
    betaHookCount_eq_tail_sub_pairs _ (by omega : 0 < h+1), coeff_occupancy, ← betaTail_sub_succ]
  ring

theorem betaHookBag_eq_of_boundaryCorr_eq {B C : Finset ℕ} {D : ℕ} (hD : 0 < D)
    (hB : ∀ b ∈ B, b < D) (hC : ∀ c ∈ C, c < D)
    (he : boundaryCorr B D = boundaryCorr C D) : betaHookBag B = betaHookBag C := by
  rw [boundaryCorr_expand hD hB, boundaryCorr_expand hD hC] at he
  have hQ := mul_left_cancel₀ (X_sub_C_ne_zero (1 : ℤ)) (add_left_cancel he)
  apply Multiset.ext'
  intro h
  by_cases hz : h = 0
  · subst h
    rw [betaHook_count_zero, betaHook_count_zero]
  have hstep (j : ℕ) (hj : 0 < j) :
      (betaHookBag B).count (j+1) = (betaHookBag C).count (j+1) →
        (betaHookBag B).count j = (betaHookBag C).count j := by
    intro he'
    have hw := congrArg (fun p : BoundaryPoly => p.coeff (D+j)) hQ
    rw [coeff_boundaryCorrQuot hD hj hB, coeff_boundaryCorrQuot hD hj hC, he'] at hw
    exact Int.ofNat_inj.mp (by omega)
  have hdown (t : ℕ) : ∀ j ≥ h, D ≤ j+t →
      (betaHookBag B).count j = (betaHookBag C).count j := by
    induction t with
    | zero =>
      intro j _ hj
      rw [betaHook_count_eq_zero_of_ge hB (by omega),
        betaHook_count_eq_zero_of_ge hC (by omega)]
    | succ t ih =>
      intro j hj ht
      exact hstep j (by omega) (ih (j+1) (by omega) (by omega))
  exact hdown D h le_rfl (by omega)

end
end LiteralColoring

#print axioms LiteralColoring.betaHookBag_eq_of_boundaryCorr_eq
```

## BoundarySeparated.lean

```lean
import BoundaryHooks
import Mathlib.Algebra.Polynomial.Expand

open Polynomial
open scoped BigOperators

namespace LiteralColoring
noncomputable section

def separatedCoeffs (q : BoundaryPoly) (D : ℕ) : Prop :=
  ∀ i ∈ q.support, ∀ j ∈ q.support, i < j → i+D < j

theorem coeff_mul_support_sum (p q : BoundaryPoly) (n : ℕ) :
    (p*q).coeff n = ∑ i ∈ q.support, if i ≤ n then p.coeff (n-i) * q.coeff i else 0 := by
  conv_lhs => rw [q.as_sum_support_C_mul_X_pow]
  rw [Finset.mul_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_assoc, coeff_mul_X_pow', coeff_mul_C]

theorem coeff_mul_inside_block {p q : BoundaryPoly} {D i j : ℕ}
    (hp : p.natDegree ≤ D) (hq : separatedCoeffs q D)
    (hi : i ∈ q.support) (hj : j ≤ D) :
    (p*q).coeff (i+j) = p.coeff j * q.coeff i := by
  rw [coeff_mul_support_sum, Finset.sum_eq_single i]
  · simp
  · intro t ht hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hg := hq t ht i hi hlt
      have h0 : p.coeff (i+j-t) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      simp [h0]
    · have hg := hq i hi t ht hgt
      exact ite_eq_right (by omega)
  · exact fun hn => (hn hi).elim

theorem coeff_mul_outside_blocks {p q : BoundaryPoly} {D n : ℕ}
    (hp : p.natDegree ≤ D)
    (hn : ∀ t ∈ q.support, ¬(t ≤ n ∧ n-t ≤ D)) :
    (p*q).coeff n = 0 := by
  rw [coeff_mul_support_sum]
  apply Finset.sum_eq_zero
  intro t ht
  by_cases hlt : t ≤ n
  · have h0 : p.coeff (n-t) = 0 := coeff_eq_zero_of_natDegree_lt (by
      have := hn t ht
      omega)
    simp [hlt,h0]
  · simp [hlt]

theorem occupancy_coeff_binary (B : Finset ℕ) (i : ℕ) :
    (occupancy B).coeff i = 0 ∨ (occupancy B).coeff i = 1 := by
  rw [coeff_occupancy]
  split <;> simp

theorem boundary_inside_block {B : Finset ℕ} {D i j : ℕ}
    (hz : 0 ∉ B) (hsep : separatedCoeffs (boundary B) D)
    (hi : i ∈ (boundary B).support) (hj : j ≤ D) :
    ((boundary B).coeff i = 1 ∧ (occupancy B).coeff (i+j) = 0) ∨
      ((boundary B).coeff i = -1 ∧ (occupancy B).coeff (i+j) = 1) := by
  have hconst : ∀ a ≤ D, (occupancy B).coeff (i+a) = (occupancy B).coeff i := by
    intro a ha
    induction a with
    | zero => rfl
    | succ a ih =>
      have hna : i+(a+1) ∉ (boundary B).support := by
        intro hm
        have hg := hsep i hi (i+(a+1)) hm (by omega)
        omega
      have hzero := notMem_support_iff.mp hna
      rw [← Nat.add_assoc, coeff_boundary_succ, sub_eq_zero] at hzero
      exact hzero.symm.trans (ih (by omega))
  rw [hconst j hj]
  cases i with
  | zero =>
    left
    exact ⟨coeff_boundary_zero _ hz, (coeff_occupancy _ _).trans (ite_eq_right hz)⟩
  | succ i =>
    have hne := mem_support_iff.mp hi
    rw [coeff_boundary_succ] at hne ⊢
    rcases occupancy_coeff_binary B i with h0 | h0 <;>
      rcases occupancy_coeff_binary B (i+1) with h1 | h1 <;> simp_all

theorem separated_boundary_mul {A B : Finset ℕ} {D : ℕ}
    (hA : ∀ a ∈ A, a < D+1) (hAz : 0 ∉ A) (hBz : 0 ∉ B)
    (hsep : separatedCoeffs (boundary B) D) :
    ∃ C : Finset ℕ, 0 ∉ C ∧ boundary C = boundary A * boundary B := by
  classical
  let p := occupancy B + occupancy A * boundary B
  have hdeg : (occupancy A).natDegree ≤ D := by simpa using natDegree_occupancy_le hA
  have hp (n : ℕ) : p.coeff n = 0 ∨ p.coeff n = 1 := by
    change (occupancy B + occupancy A * boundary B).coeff n = 0 ∨
      (occupancy B + occupancy A * boundary B).coeff n = 1
    rw [coeff_add]
    by_cases hn : ∃ i ∈ (boundary B).support, i ≤ n ∧ n-i ≤ D
    · obtain ⟨i,hi,hin,hj⟩ := hn
      obtain ⟨j,rfl⟩ : ∃ j, n = i+j := ⟨n-i,by omega⟩
      have hj' : j ≤ D := by omega
      rw [coeff_mul_inside_block hdeg hsep hi hj']
      rcases boundary_inside_block hBz hsep hi hj' with ⟨hq,hv⟩ | ⟨hq,hv⟩ <;>
        rcases occupancy_coeff_binary A j with h0 | h0 <;> simp [hq,hv,h0]
    · rw [coeff_mul_outside_blocks hdeg (by
        intro t ht h
        exact hn ⟨t,ht,h⟩), add_zero]
      exact occupancy_coeff_binary B n
  obtain ⟨C,hC⟩ := occupancy_of_binary_coefficients p hp
  refine ⟨C, ?_, ?_⟩
  · have hz : p.coeff 0 = 0 := by
      simp [p, coeff_mul, coeff_occupancy, hAz, hBz]
    rw [← hC, coeff_occupancy] at hz
    intro hc
    simp [hc] at hz
  · rw [boundary, hC]
    simp only [p, boundary]
    ring

end
end LiteralColoring

#print axioms LiteralColoring.coeff_mul_inside_block
#print axioms LiteralColoring.separated_boundary_mul
```

## BoundaryRadix.lean

```lean
import BoundarySeparated
import Mathlib.Algebra.Ring.GeomSum

open Polynomial
open scoped BigOperators

namespace LiteralColoring
noncomputable section

theorem expand_support_dvd {w i : ℕ} (hw : 0 < w) {p : BoundaryPoly}
    (hi : i ∈ (expand ℤ w p).support) : w ∣ i := by
  by_contra h
  exact (mem_support_iff.mp hi) (by simp [coeff_expand hw, h])

theorem separated_expand {w D : ℕ} (h : D < w) (q : BoundaryPoly) :
    separatedCoeffs (expand ℤ w q) D := by
  intro i hi j hj hij
  obtain ⟨a, rfl⟩ := expand_support_dvd (by omega : 0 < w) hi
  obtain ⟨b, rfl⟩ := expand_support_dvd (by omega : 0 < w) hj
  have hab : a < b := Nat.lt_of_mul_lt_mul_left hij
  have hm := Nat.mul_le_mul_left w (show a+1 ≤ b by omega)
  rw [Nat.mul_add, Nat.mul_one] at hm
  omega

theorem coeff_expand_block {w i j : ℕ} {p : BoundaryPoly}
    (hw : j < w) (hp : p.natDegree < w) (q : BoundaryPoly) :
    (p * expand ℤ w q).coeff (w*i+j) = p.coeff j * q.coeff i := by
  have hw' : 0 < w := by omega
  have he : (expand ℤ w q).coeff (w*i) = q.coeff i := coeff_expand_mul' hw' q i
  by_cases hi : w*i ∈ (expand ℤ w q).support
  · exact (coeff_mul_inside_block (D := w-1) (by omega)
      (separated_expand (by omega) q) hi (by omega)).trans (by rw [he])
  · have hz := notMem_support_iff.mp hi
    rw [he] at hz
    rw [hz, mul_zero]
    apply coeff_mul_outside_blocks (D := w-1) (by omega)
    intro t ht hbad
    obtain ⟨a,rfl⟩ := expand_support_dvd hw' ht
    have ht' : (w*a) / w = a := Nat.mul_div_cancel_left _ hw'
    have hi' : (w*i) / w = i := Nat.mul_div_cancel_left _ hw'
    have hl : a ≤ i := by
      by_contra hn
      have hmul := Nat.mul_le_mul_left w (show i+1 ≤ a by omega)
      rw [Nat.mul_add, Nat.mul_one] at hmul
      omega
    have hr : i ≤ a := by
      by_contra hn
      have hmul := Nat.mul_le_mul_left w (show a+1 ≤ i by omega)
      rw [Nat.mul_add, Nat.mul_one] at hmul
      omega
    have h' : a = i := by omega
    subst a
    exact hi ht

def radixInterval (w : ℕ) : BoundaryPoly := ∑ i ∈ Finset.range w, X^i

theorem coeff_radixInterval (w i : ℕ) : (radixInterval w).coeff i = if i < w then 1 else 0 := by
  simp [radixInterval, Polynomial.finsetSum_coeff, coeff_X_pow]

theorem radixInterval_degree_le (w : ℕ) : (radixInterval w).natDegree ≤ w-1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [coeff_radixInterval, ite_eq_right (by omega)]

theorem radixInterval_mul (w : ℕ) : (X-1 : BoundaryPoly)*radixInterval w = X^w-1 := by
  induction w with
  | zero => simp [radixInterval]
  | succ w ih =>
    rw [radixInterval, Finset.sum_range_succ, ← radixInterval, mul_add, ih, pow_succ]
    ring

theorem expand_boundary {B : Finset ℕ} (hz : 0 ∉ B) {w : ℕ} (hw : 0 < w) :
    ∃ C : Finset ℕ, 0 ∉ C ∧ boundary C = expand ℤ w (boundary B) := by
  let p := radixInterval w * expand ℤ w (occupancy B)
  have hcoeff (n : ℕ) : p.coeff n = (occupancy B).coeff (n/w) := by
    have hn : n = w*(n/w)+(n%w) := by have := Nat.mod_add_div n w; omega
    have hr := Nat.mod_lt n hw
    have hl : (radixInterval w).natDegree < w := (radixInterval_degree_le w).trans_lt (by omega)
    conv_lhs => change (radixInterval w * expand ℤ w (occupancy B)).coeff n; rw [hn]
    rw [coeff_expand_block hr hl, coeff_radixInterval, ite_eq_left hr, one_mul]
  obtain ⟨C,hC⟩ := occupancy_of_binary_coefficients p fun n => hcoeff n ▸ occupancy_coeff_binary B (n/w)
  refine ⟨C, ?_, ?_⟩
  · have hzero := hcoeff 0
    rw [← hC, Nat.zero_div, coeff_occupancy, coeff_occupancy, ite_eq_right hz] at hzero
    intro h
    rw [ite_eq_left h] at hzero
    exact one_ne_zero hzero
  · rw [boundary, hC]
    simp only [p, boundary, map_add, map_one, map_mul, map_sub, expand_X, ← mul_assoc, radixInterval_mul]

theorem expand_preserves_jet {p q : BoundaryPoly} {w r : ℕ}
    (h : (X-1 : BoundaryPoly)^r ∣ p-q) :
    (X-1 : BoundaryPoly)^r ∣ expand ℤ w p - expand ℤ w q := by
  have he : (X-1 : BoundaryPoly) ∣ X^w-1 := ⟨radixInterval w,(radixInterval_mul w).symm⟩
  rw [← map_sub]
  apply (pow_dvd_pow_of_dvd he r).trans
  simpa only [map_pow, map_sub, map_one, expand_X] using map_dvd (expand ℤ w) h

theorem reflect_expand (q : BoundaryPoly) {D w : ℕ} (hw : 0 < w) :
    (expand ℤ w q).reflect (D*w) = expand ℤ w (q.reflect D) := by
  ext n
  rw [coeff_reflect, coeff_expand hw, coeff_expand hw]
  by_cases hn : n ≤ D*w
  · rw [revAt_le hn]
    by_cases hd : w ∣ n
    · obtain ⟨a,rfl⟩ := hd
      have ha : a ≤ D := Nat.le_of_mul_le_mul_left (by simpa only [Nat.mul_comm D w] using hn) hw
      rw [Nat.mul_comm D w, ← Nat.mul_sub_left_distrib, ite_eq_left (dvd_mul_right w _),
        ite_eq_left (dvd_mul_right w _), Nat.mul_div_cancel_left _ hw, Nat.mul_div_cancel_left _ hw,
        coeff_reflect, revAt_le ha]
    · have hnd : ¬ w ∣ D*w-n := by
        intro hd'
        have hd'' := Nat.dvd_sub (dvd_mul_left w D) hd'
        have he : D*w-(D*w-n) = n := by omega
        exact hd (he ▸ hd'')
      rw [ite_eq_right hd, ite_eq_right hnd]
  · rw [revAt_eq_self_of_lt (by omega : D*w < n)]
    by_cases hd : w ∣ n
    · obtain ⟨a,rfl⟩ := hd
      have ha : D < a := by
        apply Nat.lt_of_mul_lt_mul_left (a := w)
        have ht : D*w < w*a := by omega
        simpa only [Nat.mul_comm D w] using ht
      rw [ite_eq_left (dvd_mul_right w _), ite_eq_left (dvd_mul_right w _),
        Nat.mul_div_cancel_left _ hw, coeff_reflect, revAt_eq_self_of_lt ha]
    · rw [ite_eq_right hd, ite_eq_right hd]

end
end LiteralColoring

#print axioms LiteralColoring.coeff_expand_block
#print axioms LiteralColoring.expand_boundary
#print axioms LiteralColoring.expand_preserves_jet
#print axioms LiteralColoring.reflect_expand
```

## BoundaryPadding.lean

```lean
import BoundaryRadix
import ClusterPadding

open Polynomial

namespace LiteralColoring
noncomputable section

def paddingPoly (a b u v : ℕ) : BoundaryPoly :=
  1 - X^a + X^(a+u) - X^(b+u) + X^(b+u+v)

theorem coeff_paddingPoly (a b u v n : ℕ) :
    (paddingPoly a b u v).coeff n =
      (if n=0 then 1 else 0) - (if n=a then 1 else 0) + (if n=a+u then 1 else 0)
      - (if n=b+u then 1 else 0) + (if n=b+u+v then 1 else 0) := by
  simp only [paddingPoly, coeff_add, coeff_sub, coeff_one, coeff_X_pow]

theorem padding_support_subset (a b u v : ℕ) :
    (paddingPoly a b u v).support ⊆ {0,a,a+u,b+u,b+u+v} := by
  intro i hi
  by_contra h
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
  exact (mem_support_iff.mp hi) (by simp [coeff_paddingPoly, h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2])

theorem padding_separated (D a b u v : ℕ)
    (ha : D < a) (hb : a+D < b) (hu : D < u) (hv : D < v) :
    separatedCoeffs (paddingPoly a b u v) D := by
  intro i hi j hj hij
  have hi' := padding_support_subset a b u v hi
  have hj' := padding_support_subset a b u v hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi' hj'
  rcases hi' with rfl|rfl|rfl|rfl|rfl <;>
    rcases hj' with rfl|rfl|rfl|rfl|rfl <;> omega

theorem paddingPoly_degree {a b u v : ℕ} (ha : 0 < a) (hb : a < b) (hu : 0 < u) (hv : 0 < v) :
    (paddingPoly a b u v).natDegree = b+u+v := by
  apply le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [coeff_paddingPoly]
    simp [show i ≠ 0 by omega, show i ≠ a by omega, show i ≠ a+u by omega,
      show i ≠ b+u by omega, show i ≠ b+u+v by omega]
  · apply le_natDegree_of_ne_zero
    rw [coeff_paddingPoly]
    simp only [ite_eq_right (show b+u+v ≠ 0 by omega), ite_eq_right (show b+u+v ≠ a by omega),
      ite_eq_right (show b+u+v ≠ a+u by omega), ite_eq_right (show b+u+v ≠ b+u by omega),
      ite_true, sub_zero, zero_add]
    exact one_ne_zero

theorem paddingPoly_boundary {a b u v : ℕ} (ha : 0 < a) (hb : a ≤ b) :
    ∃ B : Finset ℕ, 0 ∉ B ∧ boundary B = paddingPoly a b u v := by
  let p : BoundaryPoly := radixInterval u * X^a + radixInterval v * X^(b+u)
  have hc (n : ℕ) : p.coeff n =
      (if a ≤ n ∧ n < a+u then 1 else 0) + (if b+u ≤ n ∧ n < b+u+v then 1 else 0) := by
    change (radixInterval u * X^a + radixInterval v * X^(b+u) : BoundaryPoly).coeff n = _
    rw [coeff_add, coeff_mul_X_pow', coeff_mul_X_pow', coeff_radixInterval, coeff_radixInterval]
    by_cases hn : a ≤ n <;> by_cases hm : b+u ≤ n <;>
      simp [hn,hm, show a ≤ n → (n-a < u ↔ n < a+u) by omega,
        show b+u ≤ n → (n-(b+u) < v ↔ n < b+u+v) by omega]
  have hbits (n : ℕ) : p.coeff n = 0 ∨ p.coeff n = 1 := by
    rw [hc]
    by_cases h₁ : a ≤ n ∧ n < a+u
    · have h₂ : ¬(b+u ≤ n ∧ n < b+u+v) := by omega
      simp [h₁,h₂]
    · by_cases h₂ : b+u ≤ n ∧ n < b+u+v <;> simp [h₁,h₂]
  obtain ⟨B,hB⟩ := occupancy_of_binary_coefficients p hbits
  refine ⟨B, ?_, ?_⟩
  · have hz := hc 0
    rw [← hB, coeff_occupancy] at hz
    intro h
    simp [h,show ¬a ≤ 0 by omega,show ¬b+u ≤ 0 by omega] at hz
  · rw [boundary, hB]
    simp only [p, mul_add, ← mul_assoc, radixInterval_mul, paddingPoly, pow_add]
    ring

theorem eval_derivative_X_pow_one (n : ℕ) :
    (derivative ((X:BoundaryPoly)^n)).eval 1 = (n : ℤ) := by
  simp [derivative_X_pow]

theorem eval_derivative_twice_X_pow_one (n : ℕ) :
    (derivative (derivative ((X:BoundaryPoly)^n))).eval 1 = (n : ℤ)*((n : ℤ)-1) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [derivative_X_pow, derivative_mul, derivative_C, zero_mul, zero_add,
      eval_mul, eval_C, Nat.succ_sub_one, eval_derivative_X_pow_one]
    push_cast
    ring

theorem boundarySizeTwice_padding (a b u v : ℕ) :
    boundarySizeTwice (paddingPoly a b u v) =
      2*((a:ℤ)*(u:ℤ)+(b:ℤ)*(v:ℤ)) := by
  simp only [boundarySizeTwice, paddingPoly, derivative_add, derivative_sub, derivative_one,
    derivative_zero, eval_add, eval_sub, eval_zero, eval_derivative_X_pow_one,
    eval_derivative_twice_X_pow_one, Nat.cast_add]
  ring

end
end LiteralColoring

#print axioms LiteralColoring.padding_separated
#print axioms LiteralColoring.paddingPoly_boundary
#print axioms LiteralColoring.boundarySizeTwice_padding
```

## BoundaryFamilies.lean

```lean
import BoundarySeeds
import BoundaryPadding

open Polynomial

namespace LiteralColoring
noncomputable section

def IsBoundary (p : BoundaryPoly) : Prop := ∃ B : Finset ℕ, 0 ∉ B ∧ p = boundary B

theorem isBoundary_coeff_zero {p : BoundaryPoly} (h : IsBoundary p) : p.coeff 0 = 1 := by
  obtain ⟨B,hz,rfl⟩ := h
  exact coeff_boundary_zero B hz

theorem isBoundary_ne_zero {p : BoundaryPoly} (h : IsBoundary p) : p ≠ 0 := by
  intro hzero
  have he := isBoundary_coeff_zero h
  rw [hzero, coeff_zero] at he
  exact zero_ne_one he

theorem isBoundary_eval_one {p : BoundaryPoly} (h : IsBoundary p) : p.eval 1 = 1 := by
  obtain ⟨B,_,rfl⟩ := h
  exact boundary_eval_one B

theorem bead_lt_natDegree {B : Finset ℕ} (b : ℕ) (hb : b ∈ B) :
    b < (boundary B).natDegree := by
  let hne : B.Nonempty := ⟨b,hb⟩
  have hm := Finset.le_max' B b hb
  have he : (boundary B).natDegree = B.max' hne + 1 :=
    natDegree_boundary_eq (by omega)
      (fun c hc => Nat.lt_succ_of_le (Finset.le_max' B c hc))
      (by simpa using B.max'_mem hne)
  omega

theorem isBoundary_mul_of_separated {p q : BoundaryPoly} (hp : IsBoundary p) (hq : IsBoundary q)
    (hsep : separatedCoeffs q p.natDegree) : IsBoundary (p*q) := by
  obtain ⟨A,hAz,rfl⟩ := hp
  obtain ⟨B,hBz,rfl⟩ := hq
  obtain ⟨C,hCz,hC⟩ := separated_boundary_mul
    (fun a ha => Nat.lt_succ_of_lt (bead_lt_natDegree a ha)) hAz hBz hsep
  exact ⟨C,hCz,hC.symm⟩

theorem isBoundary_expand {p : BoundaryPoly} (hp : IsBoundary p) {w : ℕ} (hw : 0 < w) :
    IsBoundary (expand ℤ w p) := by
  obtain ⟨B,hz,rfl⟩ := hp
  obtain ⟨C,hz',he⟩ := expand_boundary hz hw
  exact ⟨C,hz',he.symm⟩

def JetEq (r : ℕ) (p q : BoundaryPoly) : Prop := (X-1 : BoundaryPoly)^r ∣ p-q

theorem JetEq.refl (r : ℕ) (p : BoundaryPoly) : JetEq r p p := by
  unfold JetEq
  rw [sub_self]
  exact dvd_zero _

theorem JetEq.symm {r : ℕ} {p q : BoundaryPoly} (h : JetEq r p q) : JetEq r q p := by
  unfold JetEq at *
  simpa only [neg_sub] using dvd_neg.mpr h

theorem JetEq.mul {r : ℕ} {p q p' q' : BoundaryPoly} (hp : JetEq r p p') (hq : JetEq r q q') :
    JetEq r (p*q) (p'*q') := by
  obtain ⟨a,ha⟩ := hp
  obtain ⟨b,hb⟩ := hq
  refine ⟨a*q+p'*b,?_⟩
  calc
    p*q-p'*q' = (p-p')*q+p'*(q-q') := by ring
    _ = _ := by rw [ha,hb]; ring

structure BoundaryFamily (r : ℕ) (ι : Type) where
  shape : ι → BoundaryPoly
  degree : ℕ
  injective : Function.Injective shape
  valid : ∀ i, IsBoundary (shape i)
  degree_eq : ∀ i, (shape i).natDegree = degree
  corr_eq : ∀ i j, shape i * (shape i).reflect degree = shape j * (shape j).reflect degree
  jet_eq : ∀ i j, JetEq r (shape i) (shape j)

theorem boundaryFamily_seed (s : ℕ) :
    ∃ A : BoundaryFamily (2*s+1) Bool, A.degree = seedLength s+2 := by
  let F := boundary (seedBeads s)
  let D := seedLength s+2
  let R := F.reflect D
  obtain ⟨⟨B,hB,hr⟩,hFD,hRD,hFR,hjet,hcorr⟩ := seed_boundary_pair s
  change R = boundary B at hr
  change F.natDegree = D at hFD
  change R.natDegree = D at hRD
  change F ≠ R at hFR
  change JetEq (2*s+1) F R at hjet
  change F * F.reflect D = R * R.reflect D at hcorr
  let p : Bool → BoundaryPoly := fun b => if b then R else F
  refine ⟨⟨p,D,?_,?_,?_,?_,?_⟩,rfl⟩
  · intro i j h
    cases i <;> cases j <;> simp_all [p]
  · intro i
    cases i
    · exact ⟨seedBeads s,seedBeads_zero s,rfl⟩
    · exact ⟨B,hB,hr⟩
  · intro i
    cases i
    · exact hFD
    · exact hRD
  · intro i j
    cases i <;> cases j
    · rfl
    · exact hcorr
    · exact hcorr.symm
    · rfl
  · intro i j
    cases i <;> cases j
    · exact JetEq.refl _ _
    · exact hjet
    · exact hjet.symm
    · exact JetEq.refl _ _

def BoundaryFamily.reindex {r : ℕ} {ι κ : Type} (A : BoundaryFamily r ι) (f : κ ↪ ι) :
    BoundaryFamily r κ :=
  ⟨A.shape ∘ f, A.degree, A.injective.comp f.injective, fun i => A.valid (f i),
    fun i => A.degree_eq (f i), fun i j => A.corr_eq (f i) (f j),
    fun i j => A.jet_eq (f i) (f j)⟩

theorem BoundaryFamily.radix {r : ℕ} {ι κ : Type}
    (A : BoundaryFamily r ι) (B : BoundaryFamily r κ) :
    ∃ C : BoundaryFamily r (ι × κ), C.degree = A.degree+B.degree*(A.degree+1) := by
  let w := A.degree+1
  have hw : 0 < w := Nat.succ_pos _
  let p : ι × κ → BoundaryPoly := fun i => A.shape i.1 * expand ℤ w (B.shape i.2)
  have ha0 (i : ι) := isBoundary_coeff_zero (A.valid i)
  have hb0 (i : κ) := isBoundary_coeff_zero (B.valid i)
  have hdeg (i : ι) : (A.shape i).natDegree < w := by
    rw [A.degree_eq]
    exact Nat.lt_succ_self _
  have hb (i : κ) := isBoundary_expand (B.valid i) hw
  refine ⟨⟨p,A.degree+B.degree*w,?_,?_,?_,?_,?_⟩,rfl⟩
  · intro i j he
    have h₁ : A.shape i.1 = A.shape j.1 := by
      ext t
      by_cases ht : t < w
      · have hc := congrArg (fun q : BoundaryPoly => q.coeff (w*0+t)) he
        simpa only [p, coeff_expand_block ht (hdeg _), hb0, mul_one] using hc
      · rw [coeff_eq_zero_of_natDegree_lt (by have := hdeg i.1; omega : (A.shape i.1).natDegree < t),
          coeff_eq_zero_of_natDegree_lt (by have := hdeg j.1; omega : (A.shape j.1).natDegree < t)]
    have h₂ : B.shape i.2 = B.shape j.2 := by
      ext t
      have hc := congrArg (fun q : BoundaryPoly => q.coeff (w*t+0)) he
      simpa only [p, coeff_expand_block hw (hdeg _), ha0, one_mul] using hc
    exact Prod.ext (A.injective h₁) (B.injective h₂)
  · intro i
    exact isBoundary_mul_of_separated (A.valid _) (hb _)
      (separated_expand (hdeg _) _)
  · intro i
    change (A.shape i.1 * expand ℤ w (B.shape i.2)).natDegree = _
    rw [natDegree_mul (isBoundary_ne_zero (A.valid _)) (isBoundary_ne_zero (hb _)),
      natDegree_expand, A.degree_eq, B.degree_eq]
  · intro i j
    have href (i : ι × κ) :
        (p i).reflect (A.degree+B.degree*w) =
          (A.shape i.1).reflect A.degree * expand ℤ w ((B.shape i.2).reflect B.degree) := by
      change (A.shape i.1 * expand ℤ w (B.shape i.2)).reflect _ = _
      rw [reflect_mul _ _ (A.degree_eq _).le
        (by rw [natDegree_expand,B.degree_eq]), reflect_expand _ hw]
    rw [href,href]
    change (_ * _)*(_ * _) = (_ * _)*(_ * _)
    calc
      _ = (A.shape i.1 * (A.shape i.1).reflect A.degree) *
          expand ℤ w (B.shape i.2 * (B.shape i.2).reflect B.degree) := by
        rw [map_mul]
        ring
      _ = (A.shape j.1 * (A.shape j.1).reflect A.degree) *
          expand ℤ w (B.shape j.2 * (B.shape j.2).reflect B.degree) := by
        rw [A.corr_eq i.1 j.1,B.corr_eq i.2 j.2]
      _ = _ := by rw [map_mul]; ring
  · intro i j
    exact (A.jet_eq i.1 j.1).mul (expand_preserves_jet (B.jet_eq i.2 j.2))

end
end LiteralColoring

#print axioms LiteralColoring.boundaryFamily_seed
#print axioms LiteralColoring.BoundaryFamily.radix
```

## BetaSetSize.lean

```lean
import BoundaryFamilies
import BetaClusterData
import Mathlib.Algebra.BigOperators.Intervals

open Polynomial
open scoped BigOperators

namespace LiteralColoring
noncomputable section

def betaSize (B : Finset ℕ) : ℕ := (∑ b ∈ B, b) - B.card*(B.card-1)/2

theorem betaAsc_ge_index (B : Finset ℕ) {ell : ℕ} (h : B.card = ell) (i : Fin ell) :
    i.val ≤ betaAsc B h i := by
  have hsub : (Finset.Iio i).map (betaAsc B h).toEmbedding ⊆
      Finset.range (betaAsc B h i) := by
    intro b hb
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hb
    exact Finset.mem_range.mpr ((betaAsc B h).strictMono (Finset.mem_Iio.mp hj))
  simpa only [Finset.card_map, Finset.card_range, Fin.card_Iio] using Finset.card_le_card hsub

theorem beta_tri_le_sum (B : Finset ℕ) :
    B.card*(B.card-1)/2 ≤ ∑ b ∈ B, b := by
  have he : (∑ i : Fin B.card, (i : ℕ)) = B.card*(B.card-1)/2 := by
    exact (Fin.sum_univ_eq_sum_range (fun x : ℕ => x) B.card).trans (Finset.sum_range_id _)
  rw [← he]
  calc
    _ ≤ ∑ i : Fin B.card, betaAsc B rfl i :=
      Finset.sum_le_sum fun i _ => betaAsc_ge_index B rfl i
    _ = _ :=
      (Finset.sum_map Finset.univ (betaAsc B rfl).toEmbedding id).symm.trans
        (congrArg (fun s : Finset ℕ => ∑ b ∈ s,b) (betaAsc_map_univ B rfl))

theorem beta_sum_eq_size_add_tri (B : Finset ℕ) :
    (∑ b ∈ B,b) = betaSize B + B.card*(B.card-1)/2 := by
  have := beta_tri_le_sum B
  unfold betaSize
  omega

theorem betaSize_le_square {B : Finset ℕ} {D : ℕ} (hB : ∀ b ∈ B, b < D) :
    betaSize B ≤ D*D := by
  have hcard : B.card ≤ D := by
    simpa only [Finset.card_range] using
      Finset.card_le_card (show B ⊆ Finset.range D from fun b hb => Finset.mem_range.mpr (hB b hb))
  have hsum : (∑ b ∈ B,b) ≤ B.card*D := by
    calc
      _ ≤ ∑ _b ∈ B,D := Finset.sum_le_sum fun b hb => (hB b hb).le
      _ = _ := by simp [Nat.mul_comm]
  exact (Nat.sub_le _ _).trans (hsum.trans (Nat.mul_le_mul_right _ hcard))

theorem boundarySizeTwice_eq_size (B : Finset ℕ) :
    boundarySizeTwice (boundary B) = 2*(betaSize B : ℤ) := by
  rw [boundarySizeTwice_boundary]
  have hs := congrArg (fun n : ℕ => (n : ℤ)) (beta_sum_eq_size_add_tri B)
  simp only [Nat.cast_sum, Nat.cast_add] at hs
  have ht₀ : (B.card*(B.card-1)/2)*2 = B.card*(B.card-1) := by
    rw [← Finset.sum_range_id, Finset.sum_range_id_mul_two]
  have ht := congrArg (fun n : ℕ => (n : ℤ)) ht₀
  simp only [Nat.cast_mul, Nat.cast_ofNat] at ht
  have hh : (B.card : ℤ) * (↑(B.card-1) : ℤ) = (B.card : ℤ) * ((B.card : ℤ)-1) := by
    by_cases h : B.card = 0
    · simp [h]
    · rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr h), Nat.cast_one]
  rw [hh] at ht
  omega

theorem betaCard_eq_of_jet {B C : Finset ℕ} {r : ℕ} (hr : 2 ≤ r)
    (hj : JetEq r (boundary B) (boundary C)) : B.card = C.card := by
  have h := occupancy_moments_of_boundary_dvd ((pow_dvd_pow (X-1 : BoundaryPoly) hr).trans hj)
    0 (Nat.le_refl 0)
  simpa using h

theorem betaSize_eq_of_jet {B C : Finset ℕ} {r : ℕ} (hr : 3 ≤ r)
    (hj : JetEq r (boundary B) (boundary C)) : betaSize B = betaSize C := by
  have hc := betaCard_eq_of_jet (by omega) hj
  have h := occupancy_moments_of_boundary_dvd ((pow_dvd_pow (X-1 : BoundaryPoly) hr).trans hj)
    1 (Nat.le_refl 1)
  simp only [pow_one] at h
  rw [← Nat.cast_sum, ← Nat.cast_sum] at h
  have he : (∑ b ∈ B,b) = ∑ b ∈ C,b := Int.ofNat_inj.mp h
  unfold betaSize
  rw [hc, he]

end
end LiteralColoring

#print axioms LiteralColoring.betaSize_le_square
#print axioms LiteralColoring.boundarySizeTwice_eq_size
#print axioms LiteralColoring.betaSize_eq_of_jet
```

## UniformBoundaryFamily.lean

```lean
import BoundaryFamilies

open Polynomial

namespace LiteralColoring
noncomputable section

def uniformRadixDegree (s : ℕ) : ℕ → ℕ
  | 0 => 0
  | m+1 => uniformRadixDegree s m + (seedLength s+2)*(uniformRadixDegree s m+1)

theorem uniformBoundaryFamily (s m : ℕ) :
    ∃ A : BoundaryFamily (2*s+1) (Fin m → Bool), A.degree = uniformRadixDegree s m := by
  induction m with
  | zero =>
    refine ⟨⟨fun _ => 1,0,fun _ _ _ => Subsingleton.elim _ _,?_,?_,?_,?_⟩,rfl⟩
    · intro i
      exact ⟨∅, Finset.notMem_empty _, by simp [boundary,occupancy]⟩
    · intro i
      exact natDegree_one
    · intro i j
      rfl
    · intro i j
      exact JetEq.refl _ _
  | succ m ih =>
    obtain ⟨A,hA⟩ := ih
    obtain ⟨B,hB⟩ := boundaryFamily_seed s
    obtain ⟨C,hC⟩ := A.radix B
    let E : (Fin (m+1) → Bool) ↪ (Fin m → Bool) × Bool :=
      ⟨fun f => (fun i => f i.succ,f 0), by
        intro f g h
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact congrArg Prod.snd h
        · exact congrFun (congrArg Prod.fst h) j⟩
    exact ⟨C.reindex E,by change C.degree = _; rw [hC,hA,hB,uniformRadixDegree]⟩

def binaryChoiceEmbedding (k : ℕ) : Fin k ↪ (Fin k → Bool) :=
  ⟨fun i j => decide (j=i), by
    intro i j h
    have he := congrFun h i
    simpa using he.symm⟩

theorem BoundaryFamily.pad {r : ℕ} {ι : Type} (A : BoundaryFamily r ι)
    (a b u v : ℕ) (ha : A.degree < a) (hb : a+A.degree < b)
    (hu : A.degree < u) (hv : A.degree < v) :
    ∃ P : BoundaryFamily r ι, ∀ i, P.shape i = A.shape i * paddingPoly a b u v := by
  let q := paddingPoly a b u v
  have hq : IsBoundary q := by
    obtain ⟨B,hB,he⟩ := paddingPoly_boundary (by omega : 0 < a) (by omega : a ≤ b)
    exact ⟨B,hB,he.symm⟩
  have hqn := isBoundary_ne_zero hq
  let p : ι → BoundaryPoly := fun i => A.shape i*q
  refine ⟨⟨p,A.degree+q.natDegree,?_,?_,?_,?_,?_⟩,fun _ => rfl⟩
  · intro i j he
    exact A.injective (mul_right_cancel₀ hqn he)
  · intro i
    apply isBoundary_mul_of_separated (A.valid i) hq
    rw [A.degree_eq]
    exact padding_separated _ _ _ _ _ ha hb hu hv
  · intro i
    change (A.shape i*q).natDegree = _
    rw [natDegree_mul (isBoundary_ne_zero (A.valid _)) hqn,A.degree_eq]
  · intro i j
    change (A.shape i*q) * (A.shape i*q).reflect _ =
      (A.shape j*q) * (A.shape j*q).reflect _
    rw [reflect_mul _ _ (A.degree_eq _).le le_rfl, reflect_mul _ _ (A.degree_eq _).le le_rfl]
    calc
      _ = (A.shape i * (A.shape i).reflect A.degree) * (q*q.reflect q.natDegree) := by ring
      _ = (A.shape j * (A.shape j).reflect A.degree) * (q*q.reflect q.natDegree) := by rw [A.corr_eq i j]
      _ = _ := by ring
  · intro i j
    exact (A.jet_eq i j).mul (JetEq.refl _ _)

end
end LiteralColoring

#print axioms LiteralColoring.uniformBoundaryFamily
#print axioms LiteralColoring.BoundaryFamily.pad
```

## UniformBetaClusters.lean

```lean
import UniformBoundaryFamily
import BetaSetSize

open Polynomial
open scoped BigOperators

namespace LiteralColoring
noncomputable section

def uniformClusterThreshold (d k : ℕ) : ℕ :=
  let D := uniformRadixDegree (d+1) k
  let a := D+1
  let b := 2*a+1
  D*D + (a+b)*a + D*b

theorem exact_beta_clusters_uniform (d k n : ℕ) (hn : uniformClusterThreshold d k ≤ n) :
    Nonempty (ExactBetaCluster d k n) := by
  classical
  let s := d+1
  let r := 2*s+1
  let D := uniformRadixDegree s k
  let a := D+1
  let b := 2*a+1
  let zeroChoice : Fin k → Bool := fun _ => false
  have hr : d+2 ≤ r := by dsimp [r,s]; omega
  have hr₁ : 3 ≤ r := by dsimp [r,s]; omega
  obtain ⟨A,hD⟩ : ∃ A : BoundaryFamily r (Fin k → Bool), A.degree = D := uniformBoundaryFamily s k
  choose B hBz hB using A.valid
  let n₀ := betaSize (B zeroChoice)
  have hBsmall (i : Fin k → Bool) (j : ℕ) (hj : j ∈ B i) : j < D := by
    have h := bead_lt_natDegree j hj
    rw [← hB i, A.degree_eq, hD] at h
    exact h
  have h₀ : n₀ ≤ D*D := betaSize_le_square (hBsmall zeroChoice)
  have hthreshold : n₀ + (a+b)*a + D*b ≤ n := by
    change D*D + (a+b)*a + D*b ≤ n at hn
    omega
  obtain ⟨u,v,hu,hv,he⟩ := cluster_padding_widths D n₀ n hthreshold
  change n = n₀ + a*u + b*v at he
  obtain ⟨P,hP⟩ := A.pad a b u v (by rw [hD]; exact Nat.lt_succ_self _)
    (by rw [hD]; dsimp [a,b]; omega) (by rwa [hD]) (by rwa [hD])
  choose C hCz hC using P.valid
  have hq : (paddingPoly a b u v).eval 1 = 1 := by
    simp [paddingPoly]
  have hsize (i : Fin k → Bool) : betaSize (C i) = n := by
    have heq := A.jet_eq i zeroChoice
    rw [hB i, hB zeroChoice] at heq
    have hs : betaSize (B i) = n₀ := betaSize_eq_of_jet hr₁ heq
    have hmul := boundarySizeTwice_mul (A.shape i) (paddingPoly a b u v) (isBoundary_eval_one (A.valid i)) hq
    have h := boundarySizeTwice_eq_size (C i)
    rw [← hC i, hP, hmul, hB i, boundarySizeTwice_eq_size, hs, boundarySizeTwice_padding] at h
    have hN := congrArg (fun n : ℕ => (n : ℤ)) he
    simp only [Nat.cast_add, Nat.cast_mul] at hN
    omega
  have hjet (i j : Fin k → Bool) : JetEq r (boundary (C i)) (boundary (C j)) := by
    rw [← hC i, ← hC j]
    exact P.jet_eq i j
  have hcard (i : Fin k → Bool) : (C i).card = (C zeroChoice).card :=
    betaCard_eq_of_jet (by omega) (hjet i zeroChoice)
  let emb := binaryChoiceEmbedding k
  refine ⟨⟨C ∘ emb, fun i => hCz (emb i), ?_, (C zeroChoice).card, fun i => hcard (emb i), ?_, ?_, ?_⟩⟩
  · intro i j hij
    apply emb.injective
    apply P.injective
    change C (emb i) = C (emb j) at hij
    rw [hC, hC, hij]
  · intro i
    change ∑ b ∈ C (emb i), b = _
    rw [beta_sum_eq_size_add_tri, hsize, hcard]
  · intro i j
    have hdeg : 0 < P.degree := by
      have h := P.degree_eq zeroChoice
      rw [hP, natDegree_mul (isBoundary_ne_zero (A.valid zeroChoice))
        (by
          intro hqz
          rw [hqz, eval_zero] at hq
          exact zero_ne_one hq),
        paddingPoly_degree (by dsimp [a]; omega) (by dsimp [a,b]; omega) (by omega) (by omega)] at h
      omega
    have hsmall (i : Fin k → Bool) (t : ℕ) (ht : t ∈ C i) : t < P.degree := by
      have h := bead_lt_natDegree t ht
      rwa [← hC i, P.degree_eq] at h
    apply betaHookBag_eq_of_boundaryCorr_eq hdeg (hsmall (emb i)) (hsmall (emb j))
    unfold boundaryCorr
    rw [← hC (emb i), ← hC (emb j)]
    exact P.corr_eq (emb i) (emb j)
  · intro i j q hq'
    have hm := occupancy_moments_of_boundary_dvd
      ((pow_dvd_pow (X-1 : BoundaryPoly) hr).trans (hjet (emb i) (emb j))) q hq'
    have hc := congrArg (Int.castRingHom ℂ) hm
    simpa only [Function.comp_apply, map_sum, map_pow, map_natCast] using hc

end
end LiteralColoring

#print axioms LiteralColoring.exact_beta_clusters_uniform
```

## UniformBoundedCharacters.lean

```lean
import UniformBetaClusters
import BetaClusterAssembly

open CategoryTheory

namespace LiteralColoring
noncomputable section

theorem bounded_character_clusters_uniform (d k n : ℕ) (hn : uniformClusterThreshold d k ≤ n) :
    BoundedCharacterCluster d k n := by
  obtain ⟨C⟩ := exact_beta_clusters_uniform d k n hn
  exact C.actual

end
end LiteralColoring

#print axioms LiteralColoring.bounded_character_clusters_uniform
```

## NativeCycleTypeBridge.lean

```lean
import CycleTypeColor
import Mathlib.GroupTheory.Perm.ViaEmbedding

namespace LiteralColoring
noncomputable section

theorem cycleType_viaEmbedding {m n : ℕ} (g : Equiv.Perm (Fin m))
    (e : Fin m ↪ Fin n) : (g.viaEmbedding e).cycleType = g.cycleType := by
  classical
  let dec : DecidablePred (fun b : Fin n => b ∈ Set.range e) := fun _ => Classical.propDecidable _
  unfold Equiv.Perm.viaEmbedding
  exact Equiv.Perm.cycleType_extendDomain _

theorem filter_fullCycleType {n : ℕ} (g : Equiv.Perm (Fin n)) :
    (fullCycleType g).filter (fun t => t ≠ 1) = g.cycleType := by
  rw [fullCycleType, Multiset.filter_add]
  have h₁ : g.cycleType.filter (fun t => t ≠ 1) = g.cycleType :=
    Multiset.filter_eq_self.mpr fun _ ht => Nat.ne_of_gt (Equiv.Perm.one_lt_of_mem_cycleType ht)
  rw [h₁]
  simp [Multiset.mem_replicate]

theorem fullCycleType_eq_iff {n : ℕ} {g h : Equiv.Perm (Fin n)} :
    fullCycleType g = fullCycleType h ↔ g.cycleType = h.cycleType := by
  constructor
  · intro ht
    simpa only [filter_fullCycleType] using congrArg (Multiset.filter (fun t : ℕ => t ≠ 1)) ht
  · intro ht
    have he : g.support.card = h.support.card := by
      rw [← Equiv.Perm.sum_cycleType, ← Equiv.Perm.sum_cycleType, ht]
    rw [fullCycleType, fullCycleType, ht, he]

end
end LiteralColoring

#print axioms LiteralColoring.cycleType_viaEmbedding
#print axioms LiteralColoring.fullCycleType_eq_iff
```

## FiniteTestCharacterTransfer.lean

```lean
import StableCharacterTests
import NativeCycleTypeBridge

open CategoryTheory

namespace LiteralColoring
noncomputable section

theorem cycleType_extendCharacterTest (x : CharacterTest) {n : ℕ} (hx : x.1 ≤ n) :
    (extendCharacterTest x hx).cycleType = x.2.cycleType := by
  exact cycleType_viaEmbedding x.2 (Fin.castLEEmb hx)

/-- The finite tests have arbitrary finite arities. Each test is extended by
fixed points before requiring equality on its full cycle type. -/
theorem finite_test_values_of_bounded_cluster (X : Finset CharacterTest) (k n : ℕ)
    (hcluster : BoundedCharacterCluster (X.sup Sigma.fst) k n) :
    ∃ W : Fin k → FDRep ℂ (Equiv.Perm (Fin n)),
      (∀ i, Simple (W i)) ∧ Function.Injective (fun i => (W i).character) ∧
      ∀ i j (g : Equiv.Perm (Fin n)),
        (∃ x ∈ X, ∃ hx : x.1 ≤ n, fullCycleType g = fullCycleType (extendCharacterTest x hx)) →
          (W i).character g = (W j).character g := by
  obtain ⟨W,hS,hI,hB⟩ := hcluster
  refine ⟨W,hS,hI,?_⟩
  intro i j g hg
  obtain ⟨x,hx,hxn,hcycle⟩ := hg
  have htype := fullCycleType_eq_iff.mp hcycle
  have ht : g.cycleType = x.2.cycleType := htype.trans (cycleType_extendCharacterTest x hxn)
  have hs : g.support.card = x.2.support.card :=
    (Equiv.Perm.sum_cycleType g).symm.trans
      ((congrArg Multiset.sum ht).trans (Equiv.Perm.sum_cycleType x.2))
  have hcard : x.2.support.card ≤ x.1 :=
    (Finset.card_le_univ x.2.support).trans_eq (Fintype.card_fin x.1)
  exact hB i j g (hs.le.trans (hcard.trans (Finset.le_sup (f := Sigma.fst) hx)))

end
end LiteralColoring

#print axioms LiteralColoring.finite_test_values_of_bounded_cluster
```

## UniformStableCharacters.lean

```lean
import UniformBoundedCharacters
import FiniteTestCharacterTransfer

open CategoryTheory

namespace LiteralColoring
noncomputable section

def stableFiniteTestThreshold (X : Finset CharacterTest) (k : ℕ) : ℕ :=
  max (X.sup Sigma.fst) (uniformClusterThreshold (X.sup Sigma.fst) k)

/-- The finite tests have arbitrary finite arities. Each test is extended by
fixed points before requiring equality on its full cycle type. -/
theorem finite_cycle_character_value_coincidence_uniform (X : Finset CharacterTest) (k n : ℕ)
    (hn : stableFiniteTestThreshold X k ≤ n) :
    ∃ W : Fin k → FDRep ℂ (Equiv.Perm (Fin n)),
      (∀ i, Simple (W i)) ∧ Function.Injective (fun i => (W i).character) ∧
      ∀ i j (g : Equiv.Perm (Fin n)),
        (∃ x ∈ X, ∃ hx : x.1 ≤ n, fullCycleType g = fullCycleType (extendCharacterTest x hx)) →
          (W i).character g = (W j).character g := by
  exact finite_test_values_of_bounded_cluster X k n
    (bounded_character_clusters_uniform _ _ _ ((le_max_right _ _).trans hn))

theorem finite_cycle_character_value_coincidence (X : Finset CharacterTest) (k : ℕ) (_hk : 1 ≤ k) :
    ∃ N : ℕ, X.sup Sigma.fst ≤ N ∧ ∀ n ≥ N,
      ∃ W : Fin k → FDRep ℂ (Equiv.Perm (Fin n)),
        (∀ i, Simple (W i)) ∧ Function.Injective (fun i => (W i).character) ∧
        ∀ i j (g : Equiv.Perm (Fin n)),
          (∃ x ∈ X, ∃ hx : x.1 ≤ n, fullCycleType g = fullCycleType (extendCharacterTest x hx)) →
            (W i).character g = (W j).character g :=
  ⟨stableFiniteTestThreshold X k, le_max_left _ _, finite_cycle_character_value_coincidence_uniform X k⟩

end
end LiteralColoring

#print axioms LiteralColoring.finite_cycle_character_value_coincidence_uniform
#print axioms LiteralColoring.finite_cycle_character_value_coincidence
```

