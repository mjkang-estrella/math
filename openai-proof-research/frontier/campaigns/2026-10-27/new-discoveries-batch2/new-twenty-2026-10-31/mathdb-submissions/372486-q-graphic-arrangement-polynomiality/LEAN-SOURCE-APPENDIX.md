# Companion Lean appendix for PAPER.md (MathDB 372486)

Ten modules: nine canonical + independent audit.

## QArr372486Field.lean

```lean
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Data.Fintype.Lattice
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.SetTheory.Cardinal.Finite

/-! MathDB 372486 (Opus r1, credit 0): the literal q-deformed arrangement over a finite
field `F`, its Whitney characteristic polynomial (thesis arXiv 2601.06546 Sec. 2), and the
finite-field evaluation `chi(q^s) = #{v : V -> F^s | v independent on every face}`. -/

noncomputable section
open scoped Classical
open Finset Module

namespace QArr372486

/-- Exact downward-closed face data (abstract simplicial complex) on `V`. -/
structure FaceData (V : Type*) where
  IsFace : Finset V → Prop
  down : ∀ {s t : Finset V}, t ⊆ s → IsFace s → IsFace t

/-- Clique complex of a simple graph: the faces are exactly the cliques. -/
def cliqueFaces {V : Type*} (G : SimpleGraph V) : FaceData V where
  IsFace s := G.IsClique (s : Set V)
  down h hs := hs.subset (Finset.coe_subset.mpr h)

theorem cliqueFaces_singleton {V : Type*} (G : SimpleGraph V) (i : V) :
    (cliqueFaces G).IsFace {i} := by
  show G.IsClique (({i} : Finset V) : Set V)
  simp

variable {V : Type*} [Fintype V] {F : Type*} [Field F]

/-- The linear form `x ↦ ∑ i, a i * x i`. -/
def form (a : V → F) : (V → F) →ₗ[F] F where
  toFun x := ∑ i, a i * x i
  map_add' x y := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem form_apply (a x : V → F) : form a x = ∑ i, a i * x i := rfl

/-- The hyperplane `ker (∑ a_i x_i)` in `V → F`. -/
def hyp (a : V → F) : Submodule F (V → F) := LinearMap.ker (form a)

/-- Thesis Def. 2.5 coefficient families: all coefficients in `F^×` on a nonempty face,
zero elsewhere (the empty face would give the zero normal and is excluded). -/
def IsDeformCoeff (Δ : FaceData V) (a : V → F) : Prop :=
  ∃ C : Finset V, Δ.IsFace C ∧ C.Nonempty ∧ (∀ i ∈ C, a i ≠ 0) ∧ ∀ i ∉ C, a i = 0

/-- NTUY Def. 1.8 coefficient families: any nonzero vector supported on a face. -/
def IsNTUYCoeff (Δ : FaceData V) (a : V → F) : Prop :=
  ∃ C : Finset V, Δ.IsFace C ∧ (∀ i ∉ C, a i = 0) ∧ a ≠ 0

theorem isDeformCoeff_iff_isNTUYCoeff (Δ : FaceData V) (a : V → F) :
    IsDeformCoeff Δ a ↔ IsNTUYCoeff Δ a := by
  constructor
  · rintro ⟨C, hC, ⟨i, hi⟩, hnz, hz⟩
    exact ⟨C, hC, hz, fun h => hnz i hi (by simp [h])⟩
  · rintro ⟨C, hC, hz, hne⟩
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    refine ⟨univ.filter (fun j => a j ≠ 0), Δ.down ?_ hC, ⟨i, by simpa using hi⟩, ?_, ?_⟩
    · intro j hj
      by_contra hjC
      exact (Finset.mem_filter.mp hj).2 (hz j hjC)
    · intro j hj
      exact (Finset.mem_filter.mp hj).2
    · intro j hj
      simpa using hj

variable [Fintype F]

/-- The q-deformed arrangement: the finite set of DISTINCT hyperplanes `hyp a`; repeated
defining forms and coincident hyperplanes are identified by `Finset.image`. -/
def arr (Δ : FaceData V) : Finset (Submodule F (V → F)) :=
  (univ.filter (fun a : V → F => IsDeformCoeff Δ a)).image hyp

theorem mem_arr (Δ : FaceData V) (H : Submodule F (V → F)) :
    H ∈ arr Δ ↔ ∃ a : V → F, IsDeformCoeff Δ a ∧ hyp a = H := by
  simp [arr]

/-- The NTUY any-nonzero-coefficient version defines the same arrangement. -/
theorem arr_eq_ntuy (Δ : FaceData V) :
    arr (F := F) Δ = (univ.filter (fun a : V → F => IsNTUYCoeff Δ a)).image hyp := by
  ext H
  simp only [mem_arr, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    isDeformCoeff_iff_isNTUYCoeff]

omit [Fintype F] in
/-- Scalar multiples of a defining form give the same hyperplane. -/
theorem hyp_smul (c : F) (hc : c ≠ 0) (a : V → F) : hyp (c • a) = hyp a := by
  ext x
  simp only [hyp, LinearMap.mem_ker, form_apply, Pi.smul_apply, smul_eq_mul, mul_assoc,
    ← Finset.mul_sum, mul_eq_zero, hc, false_or]

omit [Fintype F] in
/-- Every nonzero form defines a genuine hyperplane (codimension one). -/
theorem finrank_hyp_add_one (a : V → F) (ha : a ≠ 0) :
    finrank F (hyp a) + 1 = Fintype.card V := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  have hi' : a i ≠ 0 := by simpa using hi
  have hs : Function.Surjective (form a) := by
    intro c
    refine ⟨Pi.single i (c * (a i)⁻¹), ?_⟩
    have h1 : form a (Pi.single i (c * (a i)⁻¹)) = a i * (c * (a i)⁻¹) := by
      rw [form_apply]
      simp [Pi.single_apply]
    rw [h1, mul_comm c, ← mul_assoc, mul_inv_cancel₀ hi', one_mul]
  have h := LinearMap.finrank_range_add_finrank_ker (form a)
  rw [LinearMap.range_eq_top.2 hs, finrank_top, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card] at h
  unfold hyp
  omega

/-- Characteristic polynomial, thesis Sec. 2 (Whitney form):
`∑_{B ⊆ A} (-1)^|B| t^(dim ⋂ B)`; the empty intersection is the whole space. -/
def charPoly (A : Finset (Submodule F (V → F))) : Polynomial ℤ :=
  ∑ B ∈ A.powerset, Polynomial.C ((-1 : ℤ) ^ B.card) *
    Polynomial.X ^ finrank F (B.inf id : Submodule F (V → F))

omit [Fintype V] [Fintype F] in
theorem charPoly_eval (A : Finset (Submodule F (V → F))) (x : ℤ) :
    (charPoly A).eval x =
      ∑ B ∈ A.powerset, (-1 : ℤ) ^ B.card * x ^ finrank F (B.inf id : Submodule F (V → F)) := by
  simp only [charPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]

/-- The `s`-fold direct-product linear system of `W` inside `(F^s)^V`. -/
def lift (s : ℕ) (W : Submodule F (V → F)) : Finset (V → Fin s → F) :=
  univ.filter (fun v => ∀ j, (fun i => v i j) ∈ W)

omit [Fintype V] [Fintype F] in
theorem mem_finsetInf (B : Finset (Submodule F (V → F))) (x : V → F) :
    x ∈ B.inf id ↔ ∀ H ∈ B, x ∈ H := by
  refine Finset.induction_on B (by simp) ?_
  intro H B _ ih
  simp [Finset.inf_insert, Submodule.mem_inf, ih]

theorem inf_lift (s : ℕ) (B : Finset (Submodule F (V → F))) :
    B.inf (lift s) = lift s (B.inf id) := by
  ext v
  simp only [Finset.mem_inf, lift, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_finsetInf]
  exact ⟨fun h j H hH => h H hH j, fun h H hH j => h j H hH⟩

/-- Load-bearing dimension transfer: `#(W^s) = (q^dim W)^s`. -/
theorem card_lift (s : ℕ) (W : Submodule F (V → F)) :
    (lift s W).card = (Fintype.card F ^ finrank F W) ^ s := by
  let e : (lift s W) ≃ (Fin s → W) :=
    { toFun := fun v j => ⟨fun i => v.1 i j, (Finset.mem_filter.1 v.2).2 j⟩
      invFun := fun w => ⟨fun i j => (w j : V → F) i,
        Finset.mem_filter.2 ⟨Finset.mem_univ _, fun j => (w j).2⟩⟩
      left_inv := fun v => rfl
      right_inv := fun w => rfl }
  calc (lift s W).card = Nat.card (lift s W) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = Nat.card (Fin s → W) := Nat.card_congr e
    _ = Nat.card W ^ s := by
        rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin s), Fintype.card_fin]
    _ = (Nat.card F ^ finrank F W) ^ s := by
        rw [Module.natCard_eq_pow_finrank (K := F) (V := W)]
    _ = (Fintype.card F ^ finrank F W) ^ s := by
        rw [Nat.card_eq_fintype_card (α := F)]

theorem mem_lift_hyp (s : ℕ) (a : V → F) (v : V → Fin s → F) :
    v ∈ lift s (hyp a) ↔ ∑ i, a i • v i = 0 := by
  simp only [lift, hyp, Finset.mem_filter, Finset.mem_univ, true_and, LinearMap.mem_ker,
    form_apply, funext_iff, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]

theorem sum_eq_sum_coe {M : Type*} [AddCommMonoid M] (C : Finset V) (f : V → M)
    (hf : ∀ i ∉ C, f i = 0) : ∑ i, f i = ∑ i : C, f i := by
  rw [Finset.sum_coe_sort C f]
  exact (Finset.sum_subset (Finset.subset_univ C) (fun i _ hi => hf i hi)).symm

/-- Complement equivalence: avoiding every lifted hyperplane of the arrangement is the same
as linear independence of the vectors on every face. -/
theorem avoid_iff_indep (Δ : FaceData V) (s : ℕ) (v : V → Fin s → F) :
    (∀ H ∈ arr (F := F) Δ, v ∉ lift s H) ↔
      ∀ C : Finset V, Δ.IsFace C → LinearIndependent F (fun i : C => v i) := by
  constructor
  · intro h C hC
    rw [Fintype.linearIndependent_iff]
    intro g hg i0
    by_contra hi0
    let a : V → F := fun i => if hi : i ∈ C then g ⟨i, hi⟩ else 0
    have ha : IsDeformCoeff Δ a := by
      refine (isDeformCoeff_iff_isNTUYCoeff Δ a).2 ⟨C, hC, fun i hi => by simp [a, hi], ?_⟩
      intro h0
      apply hi0
      simpa [a] using congrFun h0 (i0 : V)
    have key : ∑ i, a i • v i = ∑ i : C, g i • v i :=
      (sum_eq_sum_coe C (fun i => a i • v i) (fun i hi => by simp [a, hi])).trans
        (Finset.sum_congr rfl (fun i _ => by simp [a]))
    exact h (hyp a) ((mem_arr Δ _).2 ⟨a, ha, rfl⟩) ((mem_lift_hyp s a v).2 (key.trans hg))
  · intro h H hH hv
    obtain ⟨a, ⟨C, hC, ⟨i, hi⟩, hnz, hz⟩, rfl⟩ := (mem_arr Δ H).1 hH
    have key : ∑ i, a i • v i = ∑ i : C, a i • v i :=
      sum_eq_sum_coe C (fun i => a i • v i) (fun j hj => by simp [hz j hj])
    have h0 := (Fintype.linearIndependent_iff.1 (h C hC)) (fun i => a i)
      (key.symm.trans ((mem_lift_hyp s a v).1 hv)) ⟨i, hi⟩
    exact hnz i hi h0

/-- The literal count of vector assignments `V → F^s` independent on every face. -/
def indepCount (Δ : FaceData V) (s : ℕ) : ℕ :=
  Nat.card {v : V → Fin s → F //
    ∀ C : Finset V, Δ.IsFace C → LinearIndependent F (fun i : C => v i)}

theorem complement_card (A : Finset (Submodule F (V → F))) (s : ℕ) :
    (((A.inf fun H => (lift s H)ᶜ).card : ℕ) : ℤ) =
      (charPoly A).eval ((Fintype.card F : ℤ) ^ s) := by
  rw [Finset.inclusion_exclusion_card_inf_compl, charPoly_eval]
  refine Finset.sum_congr rfl (fun B _ => ?_)
  rw [inf_lift, card_lift]
  push_cast
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- **Finite-field evaluation** (NTUY Thm 2.5 identity, any face data): over every finite
field `F` with `q = |F|` and every `s`, `chi(A, q^s)` is the literal vector-assignment count. -/
theorem indepCount_eq (Δ : FaceData V) (s : ℕ) :
    (indepCount (F := F) Δ s : ℤ) =
      (charPoly (arr (F := F) Δ)).eval ((Fintype.card F : ℤ) ^ s) := by
  rw [← complement_card]
  congr 1
  unfold indepCount
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun v =>
    (avoid_iff_indep Δ s v).symm.trans (by simp [Finset.mem_inf])))

/-- The literal q-deformation of the graphic arrangement (thesis Def. 2.5). -/
def graphArr (G : SimpleGraph V) : Finset (Submodule F (V → F)) := arr (cliqueFaces G)

theorem graphArr_hyperplane (G : SimpleGraph V) (H : Submodule F (V → F))
    (hH : H ∈ graphArr G) : finrank F H + 1 = Fintype.card V := by
  obtain ⟨a, ha, rfl⟩ := (mem_arr (cliqueFaces G) H).1 hH
  obtain ⟨_, _, _, hne⟩ := (isDeformCoeff_iff_isNTUYCoeff (cliqueFaces G) a).1 ha
  exact finrank_hyp_add_one a hne

theorem graph_field_count (G : SimpleGraph V) (s : ℕ) :
    (Nat.card {v : V → Fin s → F // ∀ C : Finset V, G.IsClique (C : Set V) →
        LinearIndependent F (fun i : C => v i)} : ℤ) =
      (charPoly (graphArr (F := F) G)).eval ((Fintype.card F : ℤ) ^ s) :=
  indepCount_eq (cliqueFaces G) s

/-- MathDB vertex set `[ℓ]`. -/
theorem graph_field_count_fin (ℓ : ℕ) (G : SimpleGraph (Fin ℓ)) (s : ℕ) :
    (Nat.card {v : Fin ℓ → Fin s → F // ∀ C : Finset (Fin ℓ), G.IsClique (C : Set (Fin ℓ)) →
        LinearIndependent F (fun i : C => v i)} : ℤ) =
      (charPoly (graphArr (F := F) G)).eval ((Fintype.card F : ℤ) ^ s) :=
  graph_field_count G s

end QArr372486

#print axioms QArr372486.indepCount_eq
#print axioms QArr372486.graph_field_count_fin
#print axioms QArr372486.arr_eq_ntuy
#print axioms QArr372486.graphArr_hyperplane
#print axioms QArr372486.hyp_smul
#print axioms QArr372486.cliqueFaces_singleton
```

## QArr372486Mobius.lean

```lean
import QArr372486Field
import Mathlib.Data.Nat.Choose.Sum

/-! MathDB 372486 (Opus r1, credit 0): the thesis Whitney characteristic polynomial equals the
NTUY intersection-lattice / Moebius definition `∑_{X ∈ L(A)} μ(X) t^{dim X}` (Whitney's theorem)
for every finite family of proper subspaces, in particular for the q-deformed arrangement. -/

noncomputable section
open scoped Classical
open Finset Module

namespace QArr372486

variable {V : Type*} {F : Type*} [Field F]

/-- Intersection lattice `L(A) = {⋂ B | B ⊆ A}` (NTUY Sec. 1). -/
def interLattice (A : Finset (Submodule F (V → F))) : Finset (Submodule F (V → F)) :=
  A.powerset.image (fun B => B.inf id)

/-- `μ` is the Moebius function `μ(V̂, ·)` of `L(A)` ordered by reverse inclusion:
for every `X ∈ L(A)`, `∑_{Y ∈ L(A), X ⊆ Y} μ Y = [X = whole space]`. -/
def IsMoebius (A : Finset (Submodule F (V → F))) (μ : Submodule F (V → F) → ℤ) : Prop :=
  ∀ X ∈ interLattice A,
    ∑ Y ∈ (interLattice A).filter (fun Y => X ≤ Y), μ Y = if X = ⊤ then 1 else 0

/-- NTUY definition `χ(A,t) = ∑_{X ∈ L(A)} μ(X) t^{dim X}`. -/
def moebiusCharPoly (A : Finset (Submodule F (V → F))) (μ : Submodule F (V → F) → ℤ) :
    Polynomial ℤ :=
  ∑ X ∈ interLattice A, Polynomial.C (μ X) * Polynomial.X ^ finrank F X

/-- Whitney coefficient `∑_{B ⊆ A, ⋂ B = X} (-1)^|B|`. -/
def whitneyCoeff (A : Finset (Submodule F (V → F))) (X : Submodule F (V → F)) : ℤ :=
  ∑ B ∈ A.powerset with B.inf id = X, (-1 : ℤ) ^ B.card

theorem charPoly_eq_sum_whitneyCoeff (A : Finset (Submodule F (V → F))) :
    charPoly A = moebiusCharPoly A (whitneyCoeff A) := by
  unfold charPoly moebiusCharPoly whitneyCoeff
  rw [← Finset.sum_fiberwise_of_maps_to (s := A.powerset) (t := interLattice A)
    (g := fun B => B.inf id) (fun B hB => Finset.mem_image_of_mem _ hB)]
  refine Finset.sum_congr rfl (fun X _ => ?_)
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun B hB => ?_)
  rw [(Finset.mem_filter.1 hB).2]

/-- Existence: the Whitney coefficients satisfy the Moebius recursion (no member is the
whole space). -/
theorem whitneyCoeff_isMoebius (A : Finset (Submodule F (V → F))) (hA : ⊤ ∉ A) :
    IsMoebius A (whitneyCoeff A) := by
  intro X hX
  have h1 : ∑ Y ∈ (interLattice A).filter (fun Y => X ≤ Y), whitneyCoeff A Y =
      ∑ B ∈ A.powerset.filter (fun B => X ≤ B.inf id), (-1 : ℤ) ^ B.card := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := A.powerset.filter (fun B => X ≤ B.inf id))
      (t := (interLattice A).filter (fun Y => X ≤ Y)) (g := fun B => B.inf id)
      (fun B hB => Finset.mem_filter.2
        ⟨Finset.mem_image_of_mem _ (Finset.mem_filter.1 hB).1, (Finset.mem_filter.1 hB).2⟩)]
    refine Finset.sum_congr rfl (fun Y hY => ?_)
    unfold whitneyCoeff
    rw [Finset.filter_filter]
    refine Finset.sum_congr
      (Finset.filter_congr (fun B _ => ⟨fun h => ?_, fun h => h.2⟩)) (fun _ _ => rfl)
    exact ⟨by rw [h]; exact (Finset.mem_filter.1 hY).2, h⟩
  have h2 : A.powerset.filter (fun B => X ≤ B.inf id) = (A.filter (fun H => X ≤ H)).powerset := by
    ext B
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.le_inf_iff, id_eq,
      Finset.subset_iff]
    constructor
    · rintro ⟨hs, hl⟩ H hH
      exact ⟨hs hH, hl H hH⟩
    · intro h
      exact ⟨fun H hH => (h hH).1, fun H hH => (h hH).2⟩
  rw [h1, h2, Finset.sum_powerset_neg_one_pow_card]
  by_cases hXt : X = ⊤
  · have hE : A.filter (fun H => X ≤ H) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro H hH hle
      apply hA
      rw [hXt, top_le_iff] at hle
      rw [← hle]
      exact hH
    rw [ite_eq_left_of_eq_true _ _ (eq_true hE), ite_eq_left_of_eq_true _ _ (eq_true hXt)]
  · have hE : A.filter (fun H => X ≤ H) ≠ ∅ := by
      obtain ⟨B0, hB0, rfl⟩ := Finset.mem_image.1 hX
      obtain ⟨H, hH⟩ : B0.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        rintro rfl
        exact hXt Finset.inf_empty
      exact Finset.ne_empty_of_mem (Finset.mem_filter.2
        ⟨Finset.mem_powerset.1 hB0 hH, Finset.inf_le (f := id) hH⟩)
    rw [ite_eq_right_of_eq_false _ _ (eq_false hE), ite_eq_right_of_eq_false _ _ (eq_false hXt)]

/-- Uniqueness: the Moebius recursion determines `μ` on `L(A)`. -/
theorem isMoebius_unique [Fintype V] (A : Finset (Submodule F (V → F)))
    (μ ν : Submodule F (V → F) → ℤ) (hμ : IsMoebius A μ) (hν : IsMoebius A ν) :
    ∀ X ∈ interLattice A, μ X = ν X := by
  suffices h : ∀ m, ∀ X ∈ interLattice A, Fintype.card V - finrank F X = m → μ X = ν X from
    fun X hX => h _ X hX rfl
  intro m
  refine Nat.strong_induction_on m ?_
  intro n ih X hX hn
  have hmem : X ∈ (interLattice A).filter (fun Y => X ≤ Y) :=
    Finset.mem_filter.2 ⟨hX, le_refl X⟩
  have hrest : ∑ Y ∈ ((interLattice A).filter (fun Y => X ≤ Y)).erase X, μ Y =
      ∑ Y ∈ ((interLattice A).filter (fun Y => X ≤ Y)).erase X, ν Y := by
    refine Finset.sum_congr rfl (fun Y hY => ?_)
    obtain ⟨hYX, hY'⟩ := Finset.mem_erase.1 hY
    obtain ⟨hYL, hXY⟩ := Finset.mem_filter.1 hY'
    have hlt : X < Y := lt_of_le_of_ne hXY (Ne.symm hYX)
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    have h2 := Submodule.finrank_le Y
    rw [Module.finrank_fintype_fun_eq_card] at h2
    exact ih _ (by omega) Y hYL rfl
  have e1 := hμ X hX
  have e2 := hν X hX
  rw [← Finset.add_sum_erase _ _ hmem, hrest] at e1
  rw [← Finset.add_sum_erase _ _ hmem] at e2
  exact add_right_cancel (e1.trans e2.symm)

/-- **Whitney = Moebius**: for every family of proper subspaces, the thesis Whitney polynomial
equals the NTUY lattice polynomial for any Moebius function of `L(A)`. -/
theorem charPoly_eq_moebiusCharPoly [Fintype V] (A : Finset (Submodule F (V → F)))
    (hA : ⊤ ∉ A) (μ : Submodule F (V → F) → ℤ) (hμ : IsMoebius A μ) :
    charPoly A = moebiusCharPoly A μ := by
  rw [charPoly_eq_sum_whitneyCoeff]
  unfold moebiusCharPoly
  refine Finset.sum_congr rfl (fun X hX => ?_)
  rw [isMoebius_unique A _ _ (whitneyCoeff_isMoebius A hA) hμ X hX]

variable [Fintype V] [Fintype F]

/-- No member of the q-deformed arrangement is the whole space. -/
theorem top_not_mem_arr (Δ : FaceData V) : (⊤ : Submodule F (V → F)) ∉ arr Δ := by
  intro h
  obtain ⟨a, ha, hEq⟩ := (mem_arr Δ ⊤).1 h
  obtain ⟨_, _, _, hne⟩ := (isDeformCoeff_iff_isNTUYCoeff Δ a).1 ha
  have h1 := finrank_hyp_add_one a hne
  rw [hEq, finrank_top, Module.finrank_fintype_fun_eq_card] at h1
  omega

theorem arr_isMoebius_whitney (Δ : FaceData V) :
    IsMoebius (arr (F := F) Δ) (whitneyCoeff (arr Δ)) :=
  whitneyCoeff_isMoebius _ (top_not_mem_arr Δ)

/-- Finite-field evaluation with NTUY's Moebius-lattice characteristic polynomial. -/
theorem field_count_moebius (Δ : FaceData V) (s : ℕ) (μ : Submodule F (V → F) → ℤ)
    (hμ : IsMoebius (arr Δ) μ) :
    (indepCount (F := F) Δ s : ℤ) =
      (moebiusCharPoly (arr (F := F) Δ) μ).eval ((Fintype.card F : ℤ) ^ s) := by
  rw [indepCount_eq, charPoly_eq_moebiusCharPoly _ (top_not_mem_arr Δ) μ hμ]

/-- Graph form on `[ℓ]` with the NTUY lattice definition of `χ`. -/
theorem graph_field_count_moebius (ℓ : ℕ) (G : SimpleGraph (Fin ℓ)) (s : ℕ)
    (μ : Submodule F (Fin ℓ → F) → ℤ) (hμ : IsMoebius (graphArr (F := F) G) μ) :
    (Nat.card {v : Fin ℓ → Fin s → F // ∀ C : Finset (Fin ℓ), G.IsClique (C : Set (Fin ℓ)) →
        LinearIndependent F (fun i : C => v i)} : ℤ) =
      (moebiusCharPoly (graphArr (F := F) G) μ).eval ((Fintype.card F : ℤ) ^ s) :=
  field_count_moebius (cliqueFaces G) s μ hμ

end QArr372486

#print axioms QArr372486.charPoly_eq_moebiusCharPoly
#print axioms QArr372486.isMoebius_unique
#print axioms QArr372486.arr_isMoebius_whitney
#print axioms QArr372486.field_count_moebius
#print axioms QArr372486.graph_field_count_moebius
```

## QArr372486Deletion.lean

```lean
import QArr372486Field
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-! MathDB 372486 (Opus deletion/graph-lift lane, credit 0): literal deletion of one maximal
edge, contraction as identification of its endpoints (images of faces, no closure), and the
exact count identity `#good(Δ∖e) = #good(Δ) + (q-1) #good(Δ/e)` over every finite field. -/

noncomputable section
open Finset

namespace QArr372486

theorem smul_cancel_right {F M : Type*} [Field F] [AddCommGroup M] [Module F M] {x : M}
    (hx : x ≠ 0) {c d : F} (h : c • x = d • x) : c = d := by
  by_contra hne
  have h0 : (c - d) • x = 0 := by rw [sub_smul, h, sub_self]
  exact hx (by rw [← inv_smul_smul₀ (sub_ne_zero.2 hne) x, h0, smul_zero])

theorem li_units_smul_iff {F ι M : Type*} [Field F] [AddCommGroup M] [Module F M]
    (v : ι → M) (μ : ι → Fˣ) : LinearIndependent F (μ • v) ↔ LinearIndependent F v := by
  refine ⟨fun h => ?_, fun h => h.units_smul μ⟩
  have e : μ⁻¹ • μ • v = v := by
    funext x
    simp only [Pi.smul_apply', Pi.inv_apply, inv_smul_smul]
  have h2 := h.units_smul μ⁻¹
  rwa [e] at h2

/-- Relabelling along an equivalence plus unit rescaling preserves independence. -/
theorem li_transfer {F ι κ M : Type*} [Field F] [AddCommGroup M] [Module F M] (e : ι ≃ κ)
    (f : ι → M) (g : κ → M) (μ : ι → Fˣ) (h : ∀ x, g (e x) = μ x • f x) :
    LinearIndependent F f ↔ LinearIndependent F g := by
  rw [← linearIndependent_equiv e (f := g)]
  have hg : g ∘ e = μ • f := funext fun x => by simp only [Function.comp_apply, h, Pi.smul_apply']
  rw [hg, li_units_smul_iff]

theorem li_pair_iff {F V M : Type*} [Field F] [DecidableEq V] [AddCommGroup M] [Module F M]
    (v : V → M) {a b : V} (hab : a ≠ b) :
    LinearIndependent F (fun x : ({a, b} : Finset V) => v x) ↔
      LinearIndependent F ![v a, v b] := by
  let g : Fin 2 → ({a, b} : Finset V) := fun k => ⟨![a, b] k, by fin_cases k <;> simp⟩
  have hinj : Function.Injective g := by
    intro k l hkl
    have h' : ![a, b] k = ![a, b] l := congrArg Subtype.val hkl
    fin_cases k <;> fin_cases l
    · rfl
    · exact absurd h' (by simpa using hab)
    · exact absurd h' (by simpa using hab.symm)
    · rfl
  have hsurj : Function.Surjective g := by
    rintro ⟨y, hy⟩
    rcases mem_insert.1 hy with rfl | hy
    · exact ⟨0, rfl⟩
    · exact ⟨1, Subtype.ext (mem_singleton.1 hy).symm⟩
  exact (li_transfer (Equiv.ofBijective g ⟨hinj, hsurj⟩) ![v a, v b] _ (fun _ => 1)
    (fun k => by fin_cases k <;> exact (one_smul _ _).symm)).symm

/-- Literal deletion of the edge `{i,j}`: remove every face containing both endpoints. -/
def FaceData.delete {V : Type*} (Δ : FaceData V) (i j : V) : FaceData V where
  IsFace C := Δ.IsFace C ∧ ¬ (i ∈ C ∧ j ∈ C)
  down h hs := ⟨Δ.down h hs.1, fun hij => hs.2 ⟨h hij.1, h hij.2⟩⟩

/-- `{i,j}` is a maximal face: an edge lying in no larger face. -/
def FaceData.IsMaxEdge {V : Type*} [DecidableEq V] (Δ : FaceData V) (i j : V) : Prop :=
  i ≠ j ∧ Δ.IsFace {i, j} ∧ ∀ C : Finset V, Δ.IsFace C → i ∈ C → j ∈ C → C = {i, j}

/-- For a maximal edge the deletion keeps exactly the faces other than `{i,j}`. -/
theorem FaceData.delete_isFace_iff {V : Type*} [DecidableEq V] {Δ : FaceData V} {i j : V}
    (h : Δ.IsMaxEdge i j) (C : Finset V) :
    (Δ.delete i j).IsFace C ↔ Δ.IsFace C ∧ C ≠ {i, j} := by
  show (Δ.IsFace C ∧ ¬ (i ∈ C ∧ j ∈ C)) ↔ Δ.IsFace C ∧ C ≠ {i, j}
  constructor
  · rintro ⟨hC, hn⟩
    refine ⟨hC, fun e => hn ?_⟩
    rw [e]
    simp
  · rintro ⟨hC, hne⟩
    exact ⟨hC, fun hb => hne (h.2.2 C hC hb.1 hb.2)⟩

/-- Identify `j` with `i`; the contracted vertex type is `{k // k ≠ j}`. -/
def contractMap {V : Type*} [DecidableEq V] (i j : V) (hij : i ≠ j) (k : V) : {k : V // k ≠ j} :=
  if h : k = j then ⟨i, hij⟩ else ⟨k, h⟩

theorem contractMap_ne {V : Type*} [DecidableEq V] {i j : V} (hij : i ≠ j) {k : V}
    (hk : k ≠ j) : contractMap i j hij k = ⟨k, hk⟩ := dite_eq_right hk

theorem contractMap_j {V : Type*} [DecidableEq V] {i j : V} (hij : i ≠ j) :
    contractMap i j hij j = ⟨i, hij⟩ := dite_eq_left rfl

/-- Contraction: the faces are exactly the images of the original faces (no closure). -/
def FaceData.contract {V : Type*} [DecidableEq V] (Δ : FaceData V) (i j : V) (hij : i ≠ j) :
    FaceData {k : V // k ≠ j} where
  IsFace C := ∃ D : Finset V, Δ.IsFace D ∧ D.image (contractMap i j hij) = C
  down := by
    intro s t hts hs
    obtain ⟨D, hD, rfl⟩ := hs
    refine ⟨D.filter (fun k => contractMap i j hij k ∈ t), Δ.down (filter_subset _ _) hD, ?_⟩
    ext y
    simp only [mem_image, mem_filter]
    constructor
    · rintro ⟨k, ⟨_, hk⟩, rfl⟩
      exact hk
    · intro hy
      obtain ⟨k, hk, rfl⟩ := mem_image.1 (hts hy)
      exact ⟨k, ⟨hk, hy⟩, rfl⟩

/-- Assignments independent on every face: the set counted by `indepCount`. -/
def Good {F W : Type*} [Field F] (Δ : FaceData W) (s : ℕ) (v : W → Fin s → F) : Prop :=
  ∀ C : Finset W, Δ.IsFace C → LinearIndependent F (fun i : C => v i)

/-- Reassemble a contracted assignment, putting `c • w i` at the deleted vertex `j`. -/
def extendAt {F V M : Type*} [DecidableEq V] [SMul F M] (i j : V) (hij : i ≠ j) (c : F)
    (w : {k : V // k ≠ j} → M) : V → M :=
  fun k => if h : k = j then c • w ⟨i, hij⟩ else w ⟨k, h⟩

theorem extendAt_j {F V M : Type*} [DecidableEq V] [SMul F M] {i j : V} (hij : i ≠ j) (c : F)
    (w : {k : V // k ≠ j} → M) : extendAt i j hij c w j = c • w ⟨i, hij⟩ := dite_eq_left rfl

theorem extendAt_ne {F V M : Type*} [DecidableEq V] [SMul F M] {i j : V} (hij : i ≠ j) (c : F)
    (w : {k : V // k ≠ j} → M) {k : V} (hk : k ≠ j) : extendAt i j hij c w k = w ⟨k, hk⟩ :=
  dite_eq_right hk

/-- On a face not containing both endpoints, the identification is injective, and the
family at `j` is the family at `i` rescaled by `c`; independence transfers both ways. -/
theorem li_contract_transfer {F V M : Type*} [Field F] [DecidableEq V] [AddCommGroup M]
    [Module F M] {i j : V} (hij : i ≠ j) (v : V → M) (w : {k : V // k ≠ j} → M)
    (hw : ∀ k, w k = v k) {c : F} (hc : c ≠ 0) (hv : v j = c • v i) {D : Finset V}
    (hD : ¬ (i ∈ D ∧ j ∈ D)) :
    LinearIndependent F (fun x : D => v x) ↔
      LinearIndependent F (fun y : D.image (contractMap i j hij) => w y) := by
  have hval : ∀ x ∈ D, x ≠ j → (contractMap i j hij x : V) = x := fun x _ hx => by
    rw [contractMap_ne hij hx]
  have hinj : Function.Injective (fun x : D =>
      (⟨contractMap i j hij x, mem_image_of_mem _ x.2⟩ : D.image (contractMap i j hij))) := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have e : (contractMap i j hij x : V) = contractMap i j hij y :=
      congrArg (fun z : D.image (contractMap i j hij) => ((z : {k : V // k ≠ j}) : V)) hxy
    apply Subtype.ext
    show x = y
    by_cases hxj : x = j <;> by_cases hyj : y = j
    · rw [hxj, hyj]
    · rw [hxj, contractMap_j hij, hval y hy hyj] at e
      have hiD : i ∈ D := by rw [← e] at hy; exact hy
      exact absurd ⟨hiD, hxj ▸ hx⟩ hD
    · rw [hyj, contractMap_j hij, hval x hx hxj] at e
      have hiD : i ∈ D := by rw [e] at hx; exact hx
      exact absurd ⟨hiD, hyj ▸ hy⟩ hD
    · rwa [hval x hx hxj, hval y hy hyj] at e
  have hsurj : Function.Surjective (fun x : D =>
      (⟨contractMap i j hij x, mem_image_of_mem _ x.2⟩ : D.image (contractMap i j hij))) := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
    exact ⟨⟨x, hx⟩, rfl⟩
  refine li_transfer (Equiv.ofBijective _ ⟨hinj, hsurj⟩) _ _
    (fun x => if (x : V) = j then (Units.mk0 c hc)⁻¹ else 1) (fun x => ?_)
  show w (contractMap i j hij (x : V)) =
    (if (x : V) = j then (Units.mk0 c hc)⁻¹ else 1) • v x
  rw [hw]
  by_cases hxj : (x : V) = j
  · rw [ite_eq_left hxj, Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, hxj,
      contractMap_j hij, hv, inv_smul_smul₀ hc]
  · rw [ite_eq_right hxj, one_smul, hval x x.2 hxj]

theorem good_delete_of_good {F V : Type*} [Field F] {Δ : FaceData V} {i j : V} {s : ℕ}
    {v : V → Fin s → F} (hv : Good Δ s v) : Good (Δ.delete i j) s v :=
  fun C hC => hv C hC.1

theorem good_contract_of {F V : Type*} [Field F] [DecidableEq V] {Δ : FaceData V} {i j : V}
    (hij : i ≠ j) {s : ℕ} {v : V → Fin s → F} {c : F} (hc : c ≠ 0) (hv : v j = c • v i)
    (hg : Good (Δ.delete i j) s v) : Good (Δ.contract i j hij) s (fun k => v k) := by
  rintro _ ⟨D, hD, rfl⟩
  by_cases hb : i ∈ D ∧ j ∈ D
  · have himg : (D.erase j).image (contractMap i j hij) = D.image (contractMap i j hij) := by
      refine Subset.antisymm (image_subset_image (erase_subset j D)) ?_
      intro y hy
      obtain ⟨k, hk, rfl⟩ := mem_image.1 hy
      by_cases hkj : k = j
      · rw [hkj, contractMap_j hij, ← contractMap_ne hij hij]
        exact mem_image_of_mem _ (mem_erase.2 ⟨hij, hb.1⟩)
      · exact mem_image_of_mem _ (mem_erase.2 ⟨hkj, hk⟩)
    rw [← himg]
    exact (li_contract_transfer hij v (fun k => v k) (fun _ => rfl) hc hv
      (by simp)).1 (hg _ ⟨Δ.down (erase_subset j D) hD, by simp⟩)
  · exact (li_contract_transfer hij v (fun k => v k) (fun _ => rfl) hc hv hb).1 (hg D ⟨hD, hb⟩)

theorem good_delete_of_contract {F V : Type*} [Field F] [DecidableEq V] {Δ : FaceData V}
    {i j : V} (hij : i ≠ j) {s : ℕ} {c : F} (hc : c ≠ 0) {w : {k : V // k ≠ j} → Fin s → F}
    (hw : Good (Δ.contract i j hij) s w) : Good (Δ.delete i j) s (extendAt i j hij c w) := by
  rintro D ⟨hD, hb⟩
  have hv : extendAt i j hij c w j = c • extendAt i j hij c w i := by
    rw [extendAt_j, extendAt_ne hij c w hij]
  exact (li_contract_transfer hij _ w (fun k => (extendAt_ne hij c w k.2).symm) hc hv hb).2
    (hw _ ⟨D, hD, rfl⟩)

theorem wi_ne_zero {F V : Type*} [Field F] [DecidableEq V] {Δ : FaceData V} {i j : V}
    (h : Δ.IsMaxEdge i j) {s : ℕ} {w : {k : V // k ≠ j} → Fin s → F}
    (hw : Good (Δ.contract i j h.1) s w) : w ⟨i, h.1⟩ ≠ 0 := by
  have hf : (Δ.contract i j h.1).IsFace (({i} : Finset V).image (contractMap i j h.1)) :=
    ⟨{i}, Δ.down (by simp) h.2.1, rfl⟩
  have hmem : (⟨i, h.1⟩ : {k : V // k ≠ j}) ∈ ({i} : Finset V).image (contractMap i j h.1) :=
    mem_image.2 ⟨i, mem_singleton_self i, contractMap_ne h.1 h.1⟩
  exact (hw _ hf).ne_zero ⟨⟨i, h.1⟩, hmem⟩

theorem not_good_extend {F V : Type*} [Field F] [DecidableEq V] {Δ : FaceData V} {i j : V}
    (h : Δ.IsMaxEdge i j) {s : ℕ} {c : F} {w : {k : V // k ≠ j} → Fin s → F}
    (hw : Good (Δ.contract i j h.1) s w) : ¬ Good Δ s (extendAt i j h.1 c w) := by
  intro hg
  have hli := (li_pair_iff (F := F) (extendAt i j h.1 c w) h.1).1 (hg _ h.2.1)
  rw [extendAt_ne h.1 c w h.1, extendAt_j, LinearIndependent.pair_iff' (wi_ne_zero h hw)] at hli
  exact hli c rfl

/-- A formerly invalid assignment has a unique nonzero proportionality scalar at the edge. -/
theorem exists_scalar {F V : Type*} [Field F] [DecidableEq V] {Δ : FaceData V} {i j : V}
    (h : Δ.IsMaxEdge i j) {s : ℕ} {v : V → Fin s → F} (hg : Good (Δ.delete i j) s v)
    (hn : ¬ Good Δ s v) : ∃ c : F, c ≠ 0 ∧ v j = c • v i := by
  obtain ⟨hij, hface, hmax⟩ := h
  have hvi : v i ≠ 0 := (hg {i} ⟨Δ.down (by simp) hface, by simp [hij.symm]⟩).ne_zero
    ⟨i, mem_singleton_self i⟩
  have hvj : v j ≠ 0 := (hg {j} ⟨Δ.down (by simp) hface, by simp [hij]⟩).ne_zero
    ⟨j, mem_singleton_self j⟩
  simp only [Good, not_forall] at hn
  obtain ⟨C, hC, hnli⟩ := hn
  by_cases hb : i ∈ C ∧ j ∈ C
  · obtain rfl := hmax C hC hb.1 hb.2
    rw [li_pair_iff v hij, LinearIndependent.pair_iff' hvi] at hnli
    obtain ⟨a, ha⟩ := not_forall.1 hnli
    have ha' : a • v i = v j := not_not.1 ha
    refine ⟨a, fun h0 => hvj ?_, ha'.symm⟩
    rw [← ha', h0, zero_smul]
  · exact absurd (hg C ⟨hC, hb⟩) hnli

theorem natCard_split {X : Type*} [Finite X] (P Q : X → Prop) (hQP : ∀ x, Q x → P x) :
    Nat.card {x // P x} = Nat.card {x // Q x} + Nat.card {x // P x ∧ ¬ Q x} := by
  classical
  rw [← Nat.card_sum]
  exact Nat.card_congr
    { toFun := fun x => if h : Q x.1 then Sum.inl ⟨x.1, h⟩ else Sum.inr ⟨x.1, x.2, h⟩
      invFun := fun y => Sum.elim (fun x => ⟨x.1, hQP _ x.2⟩) (fun x => ⟨x.1, x.2.1⟩) y
      left_inv := fun x => by by_cases h : Q x.1 <;> simp [h]
      right_inv := fun y => by
        rcases y with x | x
        · simp [x.2]
        · simp [x.2.2] }

/-- Explicit bijection: bad assignments ≃ (unit scalar) × (good contracted assignments). -/
theorem natCard_bad {F V : Type*} [Field F] [DecidableEq V] {Δ : FaceData V} {i j : V}
    (h : Δ.IsMaxEdge i j) (s : ℕ) :
    Nat.card {v : V → Fin s → F // Good (Δ.delete i j) s v ∧ ¬ Good Δ s v} =
      Nat.card (Fˣ × {w : {k : V // k ≠ j} → Fin s → F // Good (Δ.contract i j h.1) s w}) := by
  have hdep := fun (v : {v : V → Fin s → F // Good (Δ.delete i j) s v ∧ ¬ Good Δ s v}) =>
    exists_scalar h v.2.1 v.2.2
  refine Nat.card_congr
    { toFun := fun v => (Units.mk0 (hdep v).choose (hdep v).choose_spec.1,
        ⟨fun k => v.1 k, good_contract_of h.1 (hdep v).choose_spec.1 (hdep v).choose_spec.2 v.2.1⟩)
      invFun := fun p => ⟨extendAt i j h.1 (p.1 : F) p.2.1,
        good_delete_of_contract h.1 p.1.ne_zero p.2.2, not_good_extend h p.2.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨v, hv⟩
    apply Subtype.ext
    funext k
    show extendAt i j h.1 ((hdep ⟨v, hv⟩).choose) (fun k => v k) k = v k
    by_cases hk : k = j
    · rw [hk, extendAt_j]
      exact ((hdep ⟨v, hv⟩).choose_spec.2).symm
    · rw [extendAt_ne h.1 _ _ hk]
  · rintro ⟨u, w, hw⟩
    have hvj : extendAt i j h.1 (u : F) w j = (u : F) • extendAt i j h.1 (u : F) w i := by
      rw [extendAt_j, extendAt_ne h.1 _ w h.1]
    refine Prod.ext (Units.ext ?_) (Subtype.ext (funext fun k => ?_))
    · simp only [Units.val_mk0]
      have hs := (hdep ⟨extendAt i j h.1 (u : F) w, good_delete_of_contract h.1 u.ne_zero hw,
        not_good_extend h hw⟩).choose_spec.2
      exact smul_cancel_right (x := extendAt i j h.1 (u : F) w i)
        (by rw [extendAt_ne h.1 _ w h.1]; exact wi_ne_zero h hw) (hs.symm.trans hvj)
    · show extendAt i j h.1 (u : F) w k = w k
      rw [extendAt_ne h.1 _ w k.2]

/-- **Deletion–contraction for the literal count** (maximal edge, every finite field, every `s`). -/
theorem indepCount_delete {F V : Type*} [Field F] [Fintype F] [Fintype V] [DecidableEq V]
    {Δ : FaceData V} {i j : V} (h : Δ.IsMaxEdge i j) (s : ℕ) :
    indepCount (F := F) (Δ.delete i j) s =
      indepCount (F := F) Δ s +
        (Fintype.card F - 1) * indepCount (F := F) (Δ.contract i j h.1) s := by
  have h1 := natCard_split (Good (F := F) (Δ.delete i j) s) (Good Δ s)
    (fun _ hv => good_delete_of_good hv)
  have h2 := natCard_bad (F := F) h s
  rw [Nat.card_prod, Nat.card_units, Nat.card_eq_fintype_card (α := F)] at h2
  exact h1.trans (by rw [h2]; rfl)

/-- Integer difference form: `M(Δ∖e) - M(Δ) = (q-1) M(Δ/e)`. -/
theorem indepCount_delete_sub {F V : Type*} [Field F] [Fintype F] [Fintype V] [DecidableEq V]
    {Δ : FaceData V} {i j : V} (h : Δ.IsMaxEdge i j) (s : ℕ) :
    (indepCount (F := F) (Δ.delete i j) s : ℤ) - indepCount (F := F) Δ s =
      ((Fintype.card F : ℤ) - 1) * indepCount (F := F) (Δ.contract i j h.1) s := by
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  rw [indepCount_delete h s, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hq, Nat.cast_one]
  ring

/-- Characteristic-polynomial evaluation form of deletion–contraction at `t = q^s`. -/
theorem charPoly_delete_contract {F V : Type*} [Field F] [Fintype F] [Fintype V]
    [DecidableEq V] {Δ : FaceData V} {i j : V} (h : Δ.IsMaxEdge i j) (s : ℕ) :
    (charPoly (arr (F := F) (Δ.delete i j))).eval ((Fintype.card F : ℤ) ^ s) -
        (charPoly (arr (F := F) Δ)).eval ((Fintype.card F : ℤ) ^ s) =
      ((Fintype.card F : ℤ) - 1) *
        (charPoly (arr (F := F) (Δ.contract i j h.1))).eval ((Fintype.card F : ℤ) ^ s) := by
  rw [← indepCount_eq, ← indepCount_eq, ← indepCount_eq]
  exact indepCount_delete_sub h s

end QArr372486

#print axioms QArr372486.indepCount_delete
#print axioms QArr372486.indepCount_delete_sub
#print axioms QArr372486.charPoly_delete_contract
#print axioms QArr372486.FaceData.delete_isFace_iff
```

## QArr372486GraphLift.lean

```lean
import QArr372486Deletion
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Clique

/-! MathDB 372486 (Opus lane, credit 0): the explicit 33-vertex copy-star lift `G` of the
seven-label complex Δ' (11 facet triangles plus 26 same-label star edges) and the exact
signed identity `∑_{S ⊆ E_c} (-1)^{26-|S|} M(G - S) = (q-1)^26 M(Δ')` over every finite field. -/

noncomputable section
open Finset

namespace QArr372486
namespace Lift

/-- The 33 copy vertices `(facet index, position)`. -/
abbrev Cop := Fin 11 × Fin 3

/-- Labels of the facets 123,124,134,234,125,345,136,246,147,237,567 (labels 0-indexed). -/
def lab : Fin 11 → Fin 3 → Fin 7 :=
  ![![0, 1, 2], ![0, 1, 3], ![0, 2, 3], ![1, 2, 3], ![0, 1, 4], ![2, 3, 4], ![0, 2, 5],
    ![1, 3, 5], ![0, 3, 6], ![1, 2, 6], ![4, 5, 6]]

def labOf (x : Cop) : Fin 7 := lab x.1 x.2

/-- The first copy of each label in facet order. -/
def root : Fin 7 → Cop := ![(0, 0), (0, 1), (0, 2), (1, 2), (4, 2), (6, 2), (8, 2)]

def rt (x : Cop) : Cop := root (labOf x)

theorem lab_inj : ∀ f : Fin 11, ∀ p p' : Fin 3, lab f p = lab f p' → p = p' := by decide

theorem labOf_root : ∀ l : Fin 7, labOf (root l) = l := by decide

theorem labOf_rt (x : Cop) : labOf (rt x) = labOf x := labOf_root _

theorem rt_root (l : Fin 7) : rt (root l) = root l := by
  unfold rt
  rw [labOf_root]

theorem rt_rt (x : Cop) : rt (rt x) = rt x := rt_root _

theorem eq_of_facet_lab {x y : Cop} (h1 : x.1 = y.1) (h2 : labOf x = labOf y) : x = y := by
  obtain ⟨f, p⟩ := x
  obtain ⟨g, p'⟩ := y
  simp only at h1
  subst h1
  exact Prod.ext rfl (lab_inj f p p' h2)

theorem rt_ne_facet {x : Cop} (hx : x ≠ rt x) : x.1 ≠ (rt x).1 := fun h =>
  hx (eq_of_facet_lab h (labOf_rt x).symm)

/-- The lift graph: the 11 vertex-disjoint facet triangles plus, for every label, the star
joining its root copy to its other copies. -/
def G : SimpleGraph Cop where
  Adj x y := x ≠ y ∧ (x.1 = y.1 ∨ (labOf x = labOf y ∧ (x = rt x ∨ y = rt y)))
  symm := ⟨by
    rintro x y ⟨hne, h | ⟨hl, hr⟩⟩
    · exact ⟨Ne.symm hne, Or.inl h.symm⟩
    · exact ⟨Ne.symm hne, Or.inr ⟨hl.symm, hr.symm⟩⟩⟩
  loopless := ⟨by
    intro x h
    exact h.1 rfl⟩

/-- Non-root copies: they index the copy edges. -/
abbrev NR := {x : Cop // x ≠ rt x}

/-- The copy edge `{x, rt x}` of a non-root copy. -/
def edge (x : NR) : Sym2 Cop := s(x.1, rt x.1)

/-- The 26 same-label star (copy) edges `E_c`. -/
def Ec : Finset (Sym2 Cop) := univ.image edge

theorem card_Cop : Fintype.card Cop = 33 := by simp

theorem card_NR : Fintype.card NR = 26 := by decide

theorem edge_injective : Function.Injective edge := by
  rintro ⟨x, hx⟩ ⟨y, _⟩ h
  apply Subtype.ext
  simp only [edge, Sym2.eq_iff] at h
  rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact h1
  · exfalso
    apply hx
    rw [h1, rt_rt]

theorem card_Ec : #Ec = 26 := by
  rw [Ec, card_image_of_injective _ edge_injective, card_univ, card_NR]

theorem adj_rt {x : Cop} (hx : x ≠ rt x) : G.Adj x (rt x) :=
  ⟨hx, Or.inr ⟨(labOf_rt x).symm, Or.inr (rt_rt x).symm⟩⟩

/-- Every copy edge is an edge of `G`. -/
theorem Ec_subset_edgeSet : ∀ e ∈ Ec, e ∈ G.edgeSet := by
  intro e he
  obtain ⟨x, _, rfl⟩ := mem_image.1 he
  exact (SimpleGraph.mem_edgeSet G).2 (adj_rt x.2)

theorem adj_cross {x y : Cop} (h : G.Adj x y) (hf : x.1 ≠ y.1) :
    labOf x = labOf y ∧ (x = rt x ∨ y = rt y) :=
  h.2.resolve_left hf

/-- No copy edge lies in a triangle: a clique meeting two facets has at most two vertices. -/
theorem clique_cross {K : Finset Cop} (hK : G.IsClique (K : Set Cop)) {a b : Cop}
    (ha : a ∈ K) (hb : b ∈ K) (hab : a.1 ≠ b.1) : ∀ c ∈ K, c = a ∨ c = b := by
  intro c hc
  by_contra hne
  have hca : c ≠ a := fun e => hne (Or.inl e)
  have hcb : c ≠ b := fun e => hne (Or.inr e)
  have hab' : a ≠ b := fun e => hab (congrArg Prod.fst e)
  obtain ⟨lab_ab, root_ab⟩ := adj_cross (hK ha hb hab') hab
  have hca1 : c.1 ≠ a.1 := by
    intro e
    have hcb1 : c.1 ≠ b.1 := fun e' => hab (e.symm.trans e')
    obtain ⟨l, _⟩ := adj_cross (hK hc hb hcb) hcb1
    exact hca (eq_of_facet_lab e (l.trans lab_ab.symm))
  have hcb1 : c.1 ≠ b.1 := by
    intro e
    obtain ⟨l, _⟩ := adj_cross (hK hc ha hca) hca1
    exact hcb (eq_of_facet_lab e (l.trans lab_ab))
  obtain ⟨lca, rca⟩ := adj_cross (hK hc ha hca) hca1
  obtain ⟨_, rcb⟩ := adj_cross (hK hc hb hcb) hcb1
  have rta : rt c = rt a := by unfold rt; rw [lca]
  have rtb : rt b = rt a := by unfold rt; rw [← lab_ab]
  rcases root_ab with ha' | hb'
  · rcases rcb with hc' | hb''
    · exact hca (hc'.trans (rta.trans ha'.symm))
    · exact hab' (ha'.trans (rtb.symm.trans hb''.symm))
  · rcases rca with hc' | ha''
    · exact hcb (hc'.trans (rta.trans (rtb.symm.trans hb'.symm)))
    · exact hab' (ha''.trans (rtb.symm.trans hb'.symm))

/-- Copy edges are maximal faces of the clique complex. -/
theorem copyEdge_maximal {K : Finset Cop} (hK : G.IsClique (K : Set Cop)) {x : Cop}
    (hx : x ≠ rt x) (h1 : x ∈ K) (h2 : rt x ∈ K) : K = {rt x, x} := by
  apply Subset.antisymm
  · intro c hc
    rcases clique_cross hK h2 h1 (Ne.symm (rt_ne_facet hx)) c hc with rfl | rfl <;> simp
  · intro c hc
    rcases mem_insert.1 hc with rfl | hc
    · exact h2
    · rw [mem_singleton.1 hc]
      exact h1

/-- No unexpected cliques: a clique of `G` lies in one facet triangle or in one copy edge. -/
theorem clique_cases {K : Finset Cop} (hK : G.IsClique (K : Set Cop)) :
    (∃ f, ∀ a ∈ K, a.1 = f) ∨
      ∃ x : Cop, x ≠ rt x ∧ K ⊆ {rt x, x} ∧ x ∈ K ∧ rt x ∈ K := by
  by_cases h : ∃ a ∈ K, ∃ b ∈ K, a.1 ≠ b.1
  · right
    obtain ⟨a, ha, b, hb, hab⟩ := h
    have hab' : a ≠ b := fun e => hab (congrArg Prod.fst e)
    obtain ⟨l, hr⟩ := adj_cross (hK ha hb hab') hab
    have hsub : K ⊆ {a, b} := fun c hc => by
      rcases clique_cross hK ha hb hab c hc with rfl | rfl <;> simp
    have rtab : rt a = rt b := by unfold rt; rw [l]
    rcases hr with hra | hrb
    · refine ⟨b, fun e => hab' (hra.trans (rtab.trans e.symm)), ?_, hb, ?_⟩
      · rw [← rtab, ← hra]
        exact hsub
      · rw [← rtab, ← hra]
        exact ha
    · refine ⟨a, fun e => hab' (e.trans (rtab.trans hrb.symm)), ?_, ha, ?_⟩
      · rw [rtab, ← hrb, pair_comm]
        exact hsub
      · rw [rtab, ← hrb]
        exact hb
  · left
    by_cases hne : K.Nonempty
    · obtain ⟨a, ha⟩ := hne
      exact ⟨a.1, fun b hb => Classical.byContradiction fun hba => h ⟨b, hb, a, ha, hba⟩⟩
    · exact ⟨0, fun b hb => (hne ⟨b, hb⟩).elim⟩

/-- The literal seven-label complex Δ': the 11 facets and all their subsets. -/
def Δ7 : FaceData (Fin 7) where
  IsFace C := ∃ f : Fin 11, C ⊆ univ.image (lab f)
  down h hs := hs.imp fun _ hf => h.trans hf

theorem good_Δ7_iff {F : Type*} [Field F] {s : ℕ} (w : Fin 7 → Fin s → F) :
    Good Δ7 s w ↔ ∀ f : Fin 11, LinearIndependent F (fun p : Fin 3 => w (lab f p)) := by
  constructor
  · intro hw f
    exact (hw (univ.image (lab f)) ⟨f, Subset.refl _⟩).comp
      (fun p => ⟨lab f p, mem_image_of_mem _ (mem_univ p)⟩)
      (fun p p' e => lab_inj f p p' (congrArg Subtype.val e))
  · rintro hw C ⟨f, hf⟩
    have hex : ∀ y : C, ∃ p, lab f p = y := fun y => by
      obtain ⟨p, _, hp⟩ := mem_image.1 (hf y.2)
      exact ⟨p, hp⟩
    have key := (hw f).comp (fun y : C => (hex y).choose)
      (fun y z e => Subtype.ext ((hex y).choose_spec.symm.trans
        ((congrArg (lab f) e).trans (hex z).choose_spec)))
    convert key using 1
    funext y
    exact congrArg w (hex y).choose_spec.symm

theorem good_Δ7_ne_zero {F : Type*} [Field F] {s : ℕ} {w : Fin 7 → Fin s → F}
    (hw : Good Δ7 s w) (l : Fin 7) : w l ≠ 0 := by
  have h : w (lab (root l).1 (root l).2) ≠ 0 := ((good_Δ7_iff w).1 hw (root l).1).ne_zero _
  rwa [show lab (root l).1 (root l).2 = l from labOf_root l] at h

/-- Independence on every facet triangle. -/
def Tri {F : Type*} [Field F] {s : ℕ} (v : Cop → Fin s → F) : Prop :=
  ∀ f : Fin 11, LinearIndependent F (fun p : Fin 3 => v (f, p))

/-- Independence across the copy edge `{rt x, x}`. -/
def EdgeLI {F : Type*} [Field F] {s : ℕ} (v : Cop → Fin s → F) (x : Cop) : Prop :=
  LinearIndependent F ![v (rt x), v x]

theorem tri_ne_zero {F : Type*} [Field F] {s : ℕ} {v : Cop → Fin s → F} (ht : Tri v)
    (y : Cop) : v y ≠ 0 :=
  (ht y.1).ne_zero y.2

theorem li_mono {F V M : Type*} [Field F] [AddCommGroup M] [Module F M] {v : V → M}
    {K L : Finset V} (h : K ⊆ L) (hL : LinearIndependent F (fun y : L => v y)) :
    LinearIndependent F (fun y : K => v y) :=
  hL.comp (fun y : K => (⟨y.1, h y.2⟩ : L))
    (fun _ _ e => Subtype.ext (congrArg (fun z : L => (z : V)) e))

/-- Good assignments of the deleted subgraph `G - S` (true Mathlib clique faces). -/
theorem good_del_iff {F : Type*} [Field F] {s : ℕ} {S : Finset (Sym2 Cop)} (hS : S ⊆ Ec)
    (v : Cop → Fin s → F) :
    Good (cliqueFaces (G.deleteEdges (S : Set (Sym2 Cop)))) s v ↔
      Tri v ∧ ∀ x : NR, edge x ∉ S → EdgeLI v x.1 := by
  constructor
  · intro hg
    refine ⟨fun f => ?_, fun x hx => ?_⟩
    · have hc : (G.deleteEdges (S : Set (Sym2 Cop))).IsClique
          ((univ.image (fun p : Fin 3 => (f, p)) : Finset Cop) : Set Cop) := by
        intro a ha b hb hab
        simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range] at ha hb
        obtain ⟨p, rfl⟩ := ha
        obtain ⟨p', rfl⟩ := hb
        refine (SimpleGraph.deleteEdges_adj ..).2 ⟨⟨hab, Or.inl rfl⟩, fun hm => ?_⟩
        obtain ⟨x, _, hx⟩ := mem_image.1 (hS hm)
        simp only [edge, Sym2.eq_iff] at hx
        rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact rt_ne_facet x.2 (by rw [h2, h1])
        · exact rt_ne_facet x.2 (by rw [h2, h1])
      exact (hg _ hc).comp (fun p => ⟨(f, p), mem_image_of_mem _ (mem_univ p)⟩)
        (fun p p' e => congrArg Prod.snd (congrArg Subtype.val e))
    · have hc : (G.deleteEdges (S : Set (Sym2 Cop))).IsClique
          (({rt x.1, x.1} : Finset Cop) : Set Cop) := by
        rw [coe_pair, SimpleGraph.isClique_pair]
        intro _
        refine (SimpleGraph.deleteEdges_adj ..).2 ⟨(adj_rt x.2).symm, ?_⟩
        rw [Sym2.eq_swap]
        exact hx
      exact (li_pair_iff v (Ne.symm x.2)).1 (hg _ hc)
  · rintro ⟨ht, he⟩ K hK
    have hK' : G.IsClique (K : Set Cop) := SimpleGraph.IsClique.mono (G.deleteEdges_le _) hK
    rcases clique_cases hK' with ⟨f, hf⟩ | ⟨x, hx, hsub, h1, h2⟩
    · have key := (ht f).comp (fun y : K => (y : Cop).2)
        (fun y z e => Subtype.ext (Prod.ext ((hf _ y.2).trans (hf _ z.2).symm) e))
      convert key using 1
      funext y
      exact congrArg v (Prod.ext (hf _ y.2) rfl)
    · have hadj := (SimpleGraph.deleteEdges_adj ..).1 (hK h1 h2 hx)
      exact li_mono hsub ((li_pair_iff v (Ne.symm hx)).2 (he ⟨x, hx⟩ hadj.2))

/-- Inclusion–exclusion over the 26 copy edges, inside the triangle-independent assignments. -/
theorem sum_identity_aux {F : Type*} [Field F] [Fintype F] (s : ℕ) :
    ∑ t ∈ (univ : Finset NR).powerset, (-1 : ℤ) ^ #t *
        (Nat.card {v : Cop → Fin s → F // Tri v ∧ ∀ x ∈ t, EdgeLI v x.1} : ℤ) =
      Nat.card {v : Cop → Fin s → F // Tri v ∧ ∀ x : NR, ¬ EdgeLI v x.1} := by
  classical
  let A : NR → Finset {v : Cop → Fin s → F // Tri v} :=
    fun x => univ.filter (fun v => EdgeLI v.1 x.1)
  have hT : ∀ t : Finset NR, (#(t.inf A) : ℤ) =
      Nat.card {v : Cop → Fin s → F // Tri v ∧ ∀ x ∈ t, EdgeLI v x.1} := by
    intro t
    have hinf : t.inf A = univ.filter
        (fun v : {v : Cop → Fin s → F // Tri v} => ∀ x ∈ t, EdgeLI v.1 x.1) := by
      ext v
      simp [A, mem_inf]
    rw [hinf, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact congrArg Nat.cast (Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
      (Tri (F := F) (s := s)) (fun w => ∀ x ∈ t, EdgeLI w x.1)))
  have hall : (#((univ : Finset NR).inf fun x => (A x)ᶜ) : ℤ) =
      Nat.card {v : Cop → Fin s → F // Tri v ∧ ∀ x : NR, ¬ EdgeLI v x.1} := by
    have hinf : ((univ : Finset NR).inf fun x => (A x)ᶜ) = univ.filter
        (fun v : {v : Cop → Fin s → F // Tri v} => ∀ x : NR, ¬ EdgeLI v.1 x.1) := by
      ext v
      simp [A, mem_inf]
    rw [hinf, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact congrArg Nat.cast (Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
      (Tri (F := F) (s := s)) (fun w => ∀ x : NR, ¬ EdgeLI w x.1)))
  rw [← hall, inclusion_exclusion_card_inf_compl]
  exact sum_congr rfl fun t _ => by rw [hT t]

/-- Scalar of a copy relative to its root copy (`1` at the roots). -/
def mu {F : Type*} [Field F] (lam : NR → Fˣ) (y : Cop) : Fˣ :=
  if h : y = rt y then 1 else lam ⟨y, h⟩

theorem mu_rt {F : Type*} [Field F] (lam : NR → Fˣ) (y : Cop) : mu lam (rt y) = 1 :=
  dite_eq_left (rt_rt y).symm

theorem mu_nr {F : Type*} [Field F] (lam : NR → Fˣ) (x : NR) : mu lam x.1 = lam x :=
  dite_eq_right x.2

theorem mu_root {F : Type*} [Field F] (lam : NR → Fˣ) (l : Fin 7) : mu lam (root l) = 1 :=
  dite_eq_left (rt_root l).symm

theorem good_root_of {F : Type*} [Field F] {s : ℕ} {v : Cop → Fin s → F} (ht : Tri v)
    (hc : ∀ y, ∃ c : Fˣ, v y = (c : F) • v (rt y)) : Good Δ7 s (fun l => v (root l)) := by
  rw [good_Δ7_iff]
  intro f
  choose c hc using hc
  refine (li_transfer (Equiv.refl (Fin 3)) (fun p => v (f, p)) _ (fun p => (c (f, p))⁻¹)
    fun p => ?_).1 (ht f)
  show v (rt (f, p)) = (c (f, p))⁻¹ • v (f, p)
  rw [hc (f, p), ← Units.smul_def, inv_smul_smul]

theorem tri_of_good {F : Type*} [Field F] {s : ℕ} (lam : NR → Fˣ) {w : Fin 7 → Fin s → F}
    (hw : Good Δ7 s w) : Tri (fun y => (mu lam y : F) • w (labOf y)) := by
  intro f
  exact ((good_Δ7_iff w).1 hw f).units_smul (fun p => mu lam (f, p))

theorem not_edge_of {F : Type*} [Field F] {s : ℕ} (lam : NR → Fˣ) {w : Fin 7 → Fin s → F}
    (hw : Good Δ7 s w) (x : NR) : ¬ EdgeLI (fun y => (mu lam y : F) • w (labOf y)) x.1 := by
  intro h
  have hr : (mu lam (rt x.1) : F) • w (labOf (rt x.1)) = w (labOf x.1) := by
    rw [mu_rt, labOf_rt, Units.val_one, one_smul]
  have h0 : (mu lam (rt x.1) : F) • w (labOf (rt x.1)) ≠ 0 := by
    rw [hr]
    exact good_Δ7_ne_zero hw _
  have h' : LinearIndependent F ![(mu lam (rt x.1) : F) • w (labOf (rt x.1)),
      (mu lam x.1 : F) • w (labOf x.1)] := h
  rw [LinearIndependent.pair_iff' h0] at h'
  apply h' (lam x)
  rw [hr, mu_nr]

/-- Exact star-root fibre: assignments with every copy edge dependent are
`(unit scalars on the 26 non-root copies) × (good assignments of Δ')`. -/
theorem fibre_card {F : Type*} [Field F] (s : ℕ) :
    Nat.card {v : Cop → Fin s → F // Tri v ∧ ∀ x : NR, ¬ EdgeLI v x.1} =
      Nat.card ((NR → Fˣ) × {w : Fin 7 → Fin s → F // Good Δ7 s w}) := by
  have hdep : ∀ (v : Cop → Fin s → F), Tri v → ∀ x : NR, ¬ EdgeLI v x.1 →
      ∃ c : F, c ≠ 0 ∧ c • v (rt x.1) = v x.1 := by
    intro v ht x hx
    rw [EdgeLI, LinearIndependent.pair_iff' (tri_ne_zero ht (rt x.1))] at hx
    obtain ⟨c, hc⟩ := not_forall.1 hx
    have hc' : c • v (rt x.1) = v x.1 := not_not.1 hc
    exact ⟨c, fun e => tri_ne_zero ht x.1 (by rw [← hc', e, zero_smul]), hc'⟩
  have hrel : ∀ (v : Cop → Fin s → F), Tri v → (∀ x : NR, ¬ EdgeLI v x.1) →
      ∀ y, ∃ c : Fˣ, v y = (c : F) • v (rt y) := by
    intro v ht he y
    by_cases hy : y = rt y
    · exact ⟨1, by rw [Units.val_one, one_smul]; exact congrArg v hy⟩
    · obtain ⟨c, hc, h⟩ := hdep v ht ⟨y, hy⟩ (he ⟨y, hy⟩)
      exact ⟨Units.mk0 c hc, by rw [Units.val_mk0]; exact h.symm⟩
  refine Nat.card_congr
    { toFun := fun v => (fun x => Units.mk0 (hdep v.1 v.2.1 x (v.2.2 x)).choose
          (hdep v.1 v.2.1 x (v.2.2 x)).choose_spec.1,
        ⟨fun l => v.1 (root l), good_root_of v.2.1 (hrel v.1 v.2.1 v.2.2)⟩)
      invFun := fun p => ⟨fun y => (mu p.1 y : F) • p.2.1 (labOf y),
        tri_of_good p.1 p.2.2, not_edge_of p.1 p.2.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨v, ht, he⟩
    apply Subtype.ext
    funext y
    show (mu (F := F) _ y : F) • v (root (labOf y)) = v y
    by_cases hy : y = rt y
    · rw [mu, dite_eq_left hy, Units.val_one, one_smul]
      exact congrArg v hy.symm
    · rw [mu, dite_eq_right hy, Units.val_mk0]
      exact (hdep v ht ⟨y, hy⟩ (he ⟨y, hy⟩)).choose_spec.2
  · rintro ⟨lam, w, hw⟩
    refine Prod.ext (funext fun x => Units.ext ?_) (Subtype.ext (funext fun l => ?_))
    · show (hdep _ (tri_of_good lam hw) x (not_edge_of lam hw x)).choose = (lam x : F)
      have hs := (hdep _ (tri_of_good lam hw) x (not_edge_of lam hw x)).choose_spec.2
      have hr : (mu lam (rt x.1) : F) • w (labOf (rt x.1)) = w (labOf x.1) := by
        rw [mu_rt, labOf_rt, Units.val_one, one_smul]
      have h0 : (mu lam (rt x.1) : F) • w (labOf (rt x.1)) ≠ 0 := by
        rw [hr]
        exact good_Δ7_ne_zero hw _
      refine smul_cancel_right h0 (hs.trans ?_)
      show (mu lam x.1 : F) • w (labOf x.1) =
        (lam x : F) • ((mu lam (rt x.1) : F) • w (labOf (rt x.1)))
      rw [hr, mu_nr]
    · show (mu lam (root l) : F) • w (labOf (root l)) = w l
      rw [mu_root, labOf_root, Units.val_one, one_smul]

theorem fibre_count {F : Type*} [Field F] [Fintype F] (s : ℕ) :
    (Nat.card {v : Cop → Fin s → F // Tri v ∧ ∀ x : NR, ¬ EdgeLI v x.1} : ℤ) =
      ((Fintype.card F : ℤ) - 1) ^ 26 * indepCount (F := F) Δ7 s := by
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  rw [fibre_card, Nat.card_prod, Nat.card_fun, Nat.card_units,
    Nat.card_eq_fintype_card (α := NR), card_NR, Nat.card_eq_fintype_card (α := F),
    Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hq, Nat.cast_one]
  rfl

/-- **Exact signed lift identity** for the literal 33-vertex graph family: for every finite
field `F` and every `s`, `∑_{S ⊆ E_c} (-1)^{|E_c|-|S|} M_s(G - S) = (|F|-1)^26 M_s(Δ')`. -/
theorem lift_identity {F : Type*} [Field F] [Fintype F] (s : ℕ) :
    ∑ S ∈ Ec.powerset, (-1 : ℤ) ^ (#Ec - #S) *
        (indepCount (F := F) (cliqueFaces (G.deleteEdges (S : Set (Sym2 Cop)))) s : ℤ) =
      ((Fintype.card F : ℤ) - 1) ^ 26 * indepCount (F := F) Δ7 s := by
  rw [← fibre_count, ← sum_identity_aux]
  symm
  refine sum_nbij' (fun t => tᶜ.image edge) (fun S => univ.filter (fun x => edge x ∉ S))
    (fun t _ => mem_powerset.2 (image_subset_image (subset_univ _)))
    (fun _ _ => mem_powerset.2 (subset_univ _)) (fun t _ => ?_) (fun S hS => ?_)
    (fun t _ => ?_)
  · ext x
    simp [edge_injective.mem_finset_image]
  · rw [mem_powerset] at hS
    apply Subset.antisymm
    · intro e he
      obtain ⟨x, hx, rfl⟩ := mem_image.1 he
      simpa using hx
    · intro e he
      obtain ⟨x, _, rfl⟩ := mem_image.1 (hS he)
      exact mem_image_of_mem _ (by simpa using he)
  · have hsub : tᶜ.image edge ⊆ Ec := image_subset_image (subset_univ _)
    have hexp : #Ec - #(tᶜ.image edge) = #t := by
      rw [card_image_of_injective _ edge_injective, card_compl, card_Ec, card_NR]
      exact Nat.sub_sub_self (card_NR ▸ card_le_univ t)
    rw [hexp]
    congr 2
    show Nat.card {v : Cop → Fin s → F // Tri v ∧ ∀ x ∈ t, EdgeLI v x.1} =
      Nat.card {v : Cop → Fin s → F // Good _ s v}
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    rw [good_del_iff hsub]
    exact and_congr Iff.rfl
      ⟨fun h x hx => h x (by simpa [edge_injective.mem_finset_image] using hx),
        fun h x hx => h x (by simpa [edge_injective.mem_finset_image] using hx)⟩

/-- Graph characteristic-polynomial form of the lift identity at `t = q^s`. -/
theorem lift_identity_charPoly {F : Type*} [Field F] [Fintype F] (s : ℕ) :
    ∑ S ∈ Ec.powerset, (-1 : ℤ) ^ (#Ec - #S) *
        (charPoly (graphArr (F := F) (G.deleteEdges (S : Set (Sym2 Cop))))).eval
          ((Fintype.card F : ℤ) ^ s) =
      ((Fintype.card F : ℤ) - 1) ^ 26 *
        (charPoly (arr (F := F) Δ7)).eval ((Fintype.card F : ℤ) ^ s) := by
  rw [← indepCount_eq, ← lift_identity]
  exact sum_congr rfl fun S _ => by rw [← graph_field_count]; rfl

end Lift
end QArr372486

#print axioms QArr372486.Lift.lift_identity
#print axioms QArr372486.Lift.lift_identity_charPoly
#print axioms QArr372486.Lift.clique_cases
#print axioms QArr372486.Lift.copyEdge_maximal
#print axioms QArr372486.Lift.card_Ec
#print axioms QArr372486.Lift.Ec_subset_edgeSet
#print axioms QArr372486.Lift.good_del_iff
#print axioms QArr372486.Lift.fibre_card
```

## QArr372486LiftFacts.lean

```lean
import QArr372486GraphLift

/-! MathDB 372486 (Opus lane, credit 0): literal-fidelity facts for the 33-vertex lift. -/

open Finset

namespace QArr372486
namespace Lift

/-- The facets of Δ' are exactly the 11 listed triples 123,124,134,234,125,345,136,246,147,237,
567 (0-indexed), and they are pairwise distinct. -/
theorem facets_literal :
    (univ.image fun f : Fin 11 => univ.image (lab f)) =
      {{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}, {0, 1, 4}, {2, 3, 4}, {0, 2, 5}, {1, 3, 5},
        {0, 3, 6}, {1, 2, 6}, {4, 5, 6}} := by decide

theorem card_facets : (univ.image fun f : Fin 11 => univ.image (lab f)).card = 11 := by decide

/-- Each facet has three distinct labels, so each facet triangle has 3 vertices and 3 edges. -/
theorem card_facet (f : Fin 11) : (univ.image (lab f)).card = 3 := by
  revert f
  decide

/-- `root l` is the first copy of label `l` in facet order. -/
theorem root_first : ∀ (l : Fin 7) (f : Fin 11) (p : Fin 3), lab f p = l → (root l).1 ≤ f := by
  decide

theorem labOf_root_eq : ∀ l : Fin 7, labOf (root l) = l := labOf_root

end Lift
end QArr372486

#print axioms QArr372486.Lift.facets_literal
#print axioms QArr372486.Lift.card_facets
#print axioms QArr372486.Lift.card_facet
#print axioms QArr372486.Lift.root_first
```

## QArr372486Frame.lean

```lean
import QArr372486LiftFacts
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-! MathDB 372486 (Opus projective-count lane, credit 0): frame normalisation of the actual
`Lift.Δ7` count at `s = 3`: `indepCount Δ7 3 = #{bases} * (q-1)^6 * N6`. -/

noncomputable section
open scoped Classical
open Finset Matrix

namespace QArr372486
namespace Count

variable {F : Type*} [Field F]

/-- Determinant of the three vectors of facet `f`. -/
def fdet (w : Fin 7 → Fin 3 → F) (f : Fin 11) : F :=
  (Matrix.of fun p : Fin 3 => w (Lift.lab f p)).det

/-- Every facet triple has nonzero determinant. -/
def Good7 (w : Fin 7 → Fin 3 → F) : Prop := ∀ f : Fin 11, fdet w f ≠ 0

theorem li_iff_det (r : Fin 3 → Fin 3 → F) :
    LinearIndependent F r ↔ (Matrix.of r).det ≠ 0 := by
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
    ← Matrix.linearIndependent_rows_iff_isUnit]
  rfl

theorem good_iff (w : Fin 7 → Fin 3 → F) : Good Lift.Δ7 3 w ↔ Good7 w := by
  rw [Lift.good_Δ7_iff]
  exact forall_congr' fun f => li_iff_det _

theorem indepCount_Δ7 :
    indepCount (F := F) Lift.Δ7 3 = Nat.card {w : Fin 7 → Fin 3 → F // Good7 w} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun w => good_iff w)

theorem fdet_transport (σ : Fin 7 → F) (R : Matrix (Fin 3) (Fin 3) F)
    (u : Fin 7 → Fin 3 → F) (f : Fin 11) :
    fdet (fun i => σ i • vecMul (u i) R) f =
      (∏ p : Fin 3, σ (Lift.lab f p)) * (fdet u f * R.det) := by
  have h : (Matrix.of fun p : Fin 3 => σ (Lift.lab f p) • vecMul (u (Lift.lab f p)) R) =
      Matrix.diagonal (fun p => σ (Lift.lab f p)) * ((Matrix.of fun p => u (Lift.lab f p)) * R) := by
    ext p j
    rw [Matrix.diagonal_mul]
    simp [Matrix.mul_apply, vecMul, dotProduct]
  unfold fdet
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]

theorem good7_transport (σ : Fin 7 → F) (hσ : ∀ i, σ i ≠ 0) (R : Matrix (Fin 3) (Fin 3) F)
    (hR : R.det ≠ 0) (u : Fin 7 → Fin 3 → F) :
    Good7 (fun i => σ i • vecMul (u i) R) ↔ Good7 u := by
  refine forall_congr' fun f => ?_
  rw [fdet_transport]
  have hp : (∏ p : Fin 3, σ (Lift.lab f p)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun p _ => hσ _
  constructor
  · intro h h0
    exact h (by rw [h0, zero_mul, mul_zero])
  · intro h
    exact mul_ne_zero hp (mul_ne_zero h hR)

theorem good7_transport1 (R : Matrix (Fin 3) (Fin 3) F) (hR : R.det ≠ 0)
    (u : Fin 7 → Fin 3 → F) : Good7 (fun i => vecMul (u i) R) ↔ Good7 u := by
  have := good7_transport (fun _ => (1 : F)) (fun _ => one_ne_zero) R hR u
  simpa only [one_smul] using this

def ev (i : Fin 3) : Fin 3 → F := Pi.single i 1

/-- Frame configuration `e0, e1, e2, c0, c1, c2, c3`. -/
def stdA (c : Fin 4 → Fin 3 → F) : Fin 7 → Fin 3 → F :=
  ![ev 0, ev 1, ev 2, c 0, c 1, c 2, c 3]

theorem ev_vecMul (i : Fin 3) (R : Matrix (Fin 3) (Fin 3) F) : vecMul (ev i) R = R i :=
  Matrix.single_one_vecMul i R

def rows (w : Fin 7 → Fin 3 → F) : Fin 3 → Fin 3 → F := ![w 0, w 1, w 2]

theorem fdet_zero (w : Fin 7 → Fin 3 → F) : fdet w 0 = (Matrix.of (rows w)).det := by
  unfold fdet rows
  congr 1
  ext p j
  fin_cases p <;> rfl

theorem li_rows {w : Fin 7 → Fin 3 → F} (hw : Good7 w) : LinearIndependent F (rows w) :=
  (li_iff_det _).2 (fdet_zero w ▸ hw 0)

def coA (w : Fin 7 → Fin 3 → F) : Fin 4 → Fin 3 → F :=
  ![vecMul (w 3) (Matrix.of (rows w))⁻¹, vecMul (w 4) (Matrix.of (rows w))⁻¹,
    vecMul (w 5) (Matrix.of (rows w))⁻¹, vecMul (w 6) (Matrix.of (rows w))⁻¹]

theorem recon_A (w : Fin 7 → Fin 3 → F) (hR : (Matrix.of (rows w)).det ≠ 0) :
    (fun i => vecMul (stdA (coA w) i) (Matrix.of (rows w))) = w := by
  have hu : IsUnit (Matrix.of (rows w)).det := isUnit_iff_ne_zero.2 hR
  have hk : ∀ k : Fin 7, vecMul (vecMul (w k) (Matrix.of (rows w))⁻¹) (Matrix.of (rows w)) = w k :=
    fun k => by rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
  have he : ∀ k : Fin 3, vecMul (ev k) (Matrix.of (rows w)) = rows w k :=
    fun k => ev_vecMul k _
  funext i
  fin_cases i
  exacts [he 0, he 1, he 2, hk 3, hk 4, hk 5, hk 6]

/-- Step A: normalise the first three vectors to the standard basis. -/
def eqvA : {w : Fin 7 → Fin 3 → F // Good7 w} ≃
    {r : Fin 3 → Fin 3 → F // LinearIndependent F r} ×
      {c : Fin 4 → Fin 3 → F // Good7 (stdA c)} where
  toFun w := (⟨rows w.1, li_rows w.2⟩, ⟨coA w.1, by
      have hR := (li_iff_det _).1 (li_rows w.2)
      have h : Good7 (fun i => vecMul (stdA (coA w.1) i) (Matrix.of (rows w.1))) := by
        rw [recon_A w.1 hR]; exact w.2
      exact (good7_transport1 _ hR _).1 h⟩)
  invFun p := ⟨fun i => vecMul (stdA p.2.1 i) (Matrix.of p.1.1),
      (good7_transport1 _ ((li_iff_det _).1 p.1.2) _).2 p.2.2⟩
  left_inv w := Subtype.ext (recon_A w.1 ((li_iff_det _).1 (li_rows w.2)))
  right_inv p := by
    obtain ⟨⟨r, hr⟩, ⟨c, hc⟩⟩ := p
    have hu : IsUnit (Matrix.of r).det := isUnit_iff_ne_zero.2 ((li_iff_det _).1 hr)
    have hrows : rows (fun i => vecMul (stdA c i) (Matrix.of r)) = r := by
      funext i j
      fin_cases i <;> simp [rows, stdA, ev_vecMul]
    refine Prod.ext (Subtype.ext hrows) (Subtype.ext ?_)
    show coA (fun i => vecMul (stdA c i) (Matrix.of r)) = c
    unfold coA
    rw [hrows]
    funext k j
    fin_cases k <;> simp [stdA, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu,
      Matrix.vecMul_one]

theorem card_bases [Fintype F] :
    Nat.card {r : Fin 3 → Fin 3 → F // LinearIndependent F r} =
      ∏ i : Fin 3, (Fintype.card F ^ 3 - Fintype.card F ^ (i : ℕ)) := by
  have h := card_linearIndependent (K := F) (V := Fin 3 → F) (k := 3)
    (by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin])
  rw [h, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- `det((a,b,1),(c,1,d),(1,e,f))`. -/
def Dx (a b c d e f : F) : F := (b * d - 1) + (c - a * d) * e + (a - b * c) * f

abbrev T6 (F : Type*) := F × F × F × F × F × F

def vX (t : T6 F) : Fin 3 → F := ![t.1, t.2.1, 1]
def vY (t : T6 F) : Fin 3 → F := ![t.2.2.1, 1, t.2.2.2.1]
def vZ (t : T6 F) : Fin 3 → F := ![1, t.2.2.2.2.1, t.2.2.2.2.2]

/-- Normalised configuration `e0,e1,e2,(1,1,1),(a,b,1),(c,1,d),(1,e,f)`. -/
def nrmT (t : T6 F) : Fin 7 → Fin 3 → F := ![ev 0, ev 1, ev 2, ![1, 1, 1], vX t, vY t, vZ t]

/-- The affine condition counted by `N6`. -/
def NG (t : T6 F) : Prop :=
  t.1 ≠ t.2.1 ∧ t.2.2.1 ≠ t.2.2.2.1 ∧ t.2.2.2.2.1 ≠ t.2.2.2.2.2 ∧
    Dx t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2 ≠ 0

def nvals (t : T6 F) : Fin 11 → F :=
  ![1, 1, -1, 1, 1, t.2.1 - t.1, -1, t.2.2.1 - t.2.2.2.1, t.2.2.2.2.2 - t.2.2.2.2.1, 1,
    Dx t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2]

theorem fdet_nrmT (t : T6 F) (k : Fin 11) : fdet (nrmT t) k = nvals t k := by
  obtain ⟨a, b, c, d, e, f⟩ := t
  fin_cases k <;>
    simp [fdet, nrmT, nvals, vX, vY, vZ, ev, Lift.lab, Matrix.det_fin_three, Dx] <;> ring

theorem good7_nrmT (t : T6 F) : Good7 (nrmT t) ↔ NG t := by
  obtain ⟨a, b, c, d, e, f⟩ := t
  unfold Good7 NG
  simp only [fdet_nrmT]
  constructor
  · intro h
    exact ⟨fun hh => h 5 (show b - a = 0 by rw [hh, sub_self]),
      fun hh => h 7 (show c - d = 0 by rw [hh, sub_self]),
      fun hh => h 8 (show f - e = 0 by rw [hh, sub_self]), fun hh => h 10 hh⟩
  · rintro ⟨h1, h2, h3, h4⟩ k
    have h1' : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
    have h2' : c - d ≠ 0 := sub_ne_zero.2 h2
    have h3' : f - e ≠ 0 := sub_ne_zero.2 (Ne.symm h3)
    have m1 : (-1 : F) ≠ 0 := neg_ne_zero.2 one_ne_zero
    fin_cases k
    exacts [one_ne_zero, one_ne_zero, m1, one_ne_zero, one_ne_zero, h1', m1, h2', h3',
      one_ne_zero, h4]

def cB (d s : Fin 3 → Fˣ) (t : T6 F) : Fin 4 → Fin 3 → F :=
  ![fun j => (d j : F), fun j => (s 0 : F) * (vX t j * d j), fun j => (s 1 : F) * (vY t j * d j),
    fun j => (s 2 : F) * (vZ t j * d j)]

def σB (d s : Fin 3 → Fˣ) : Fin 7 → F :=
  ![(((d 0)⁻¹ : Fˣ) : F), (((d 1)⁻¹ : Fˣ) : F), (((d 2)⁻¹ : Fˣ) : F), 1, s 0, s 1, s 2]

theorem stdA_cB (d s : Fin 3 → Fˣ) (t : T6 F) :
    stdA (cB d s t) = fun i => σB d s i • vecMul (nrmT t i) (diagonal fun j => (d j : F)) := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [stdA, cB, σB, nrmT, vX, vY, vZ, ev, Matrix.vecMul_diagonal]

theorem good_cB (d s : Fin 3 → Fˣ) (t : T6 F) : Good7 (stdA (cB d s t)) ↔ NG t := by
  have hσ : ∀ i, σB d s i ≠ 0 := by
    intro i
    fin_cases i <;> simp [σB]
  have hD : (diagonal fun j => (d j : F)).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun j _ => (d j).ne_zero
  rw [stdA_cB, good7_transport _ hσ _ hD, good7_nrmT]

theorem nz_of_good {c : Fin 4 → Fin 3 → F} (hc : Good7 (stdA c)) :
    c 0 0 ≠ 0 ∧ c 0 1 ≠ 0 ∧ c 0 2 ≠ 0 ∧ c 1 2 ≠ 0 ∧ c 2 1 ≠ 0 ∧ c 3 0 ≠ 0 := by
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  have h4 := hc 4
  have h6 := hc 6
  have h9 := hc 9
  simp [fdet, stdA, ev, Lift.lab, Matrix.det_fin_three] at h1 h2 h3 h4 h6 h9
  exact ⟨h3, h2, h1, h4, h6, h9⟩

def dOf {c : Fin 4 → Fin 3 → F} (hc : Good7 (stdA c)) : Fin 3 → Fˣ :=
  ![Units.mk0 _ (nz_of_good hc).1, Units.mk0 _ (nz_of_good hc).2.1, Units.mk0 _ (nz_of_good hc).2.2.1]

def sOf {c : Fin 4 → Fin 3 → F} (hc : Good7 (stdA c)) : Fin 3 → Fˣ :=
  ![Units.mk0 (c 1 2 / c 0 2) (div_ne_zero (nz_of_good hc).2.2.2.1 (nz_of_good hc).2.2.1),
    Units.mk0 (c 2 1 / c 0 1) (div_ne_zero (nz_of_good hc).2.2.2.2.1 (nz_of_good hc).2.1),
    Units.mk0 (c 3 0 / c 0 0) (div_ne_zero (nz_of_good hc).2.2.2.2.2 (nz_of_good hc).1)]

def tOf (c : Fin 4 → Fin 3 → F) : T6 F :=
  (c 1 0 / (c 1 2 / c 0 2 * c 0 0), c 1 1 / (c 1 2 / c 0 2 * c 0 1),
    c 2 0 / (c 2 1 / c 0 1 * c 0 0), c 2 2 / (c 2 1 / c 0 1 * c 0 2),
    c 3 1 / (c 3 0 / c 0 0 * c 0 1), c 3 2 / (c 3 0 / c 0 0 * c 0 2))

theorem recon_B {c : Fin 4 → Fin 3 → F} (hc : Good7 (stdA c)) :
    cB (dOf hc) (sOf hc) (tOf c) = c := by
  obtain ⟨n00, n01, n02, n12, n21, n30⟩ := nz_of_good hc
  funext k j
  fin_cases k <;> fin_cases j <;> simp [cB, dOf, sOf, tOf, vX, vY, vZ] <;> field_simp

theorem dOf_cB (d s : Fin 3 → Fˣ) (t : T6 F) (h : Good7 (stdA (cB d s t))) : dOf h = d := by
  funext j
  apply Units.ext
  fin_cases j <;> simp [dOf, cB]

theorem sOf_cB (d s : Fin 3 → Fˣ) (t : T6 F) (h : Good7 (stdA (cB d s t))) : sOf h = s := by
  funext j
  apply Units.ext
  have := (d 0).ne_zero
  have := (d 1).ne_zero
  have := (d 2).ne_zero
  fin_cases j <;> simp [sOf, cB, vX, vY, vZ]

theorem tOf_cB (d s : Fin 3 → Fˣ) (t : T6 F) : tOf (cB d s t) = t := by
  obtain ⟨a, b, c, d', e, f⟩ := t
  have := (d 0).ne_zero
  have := (d 1).ne_zero
  have := (d 2).ne_zero
  have := (s 0).ne_zero
  have := (s 1).ne_zero
  have := (s 2).ne_zero
  simp only [tOf, cB, vX, vY, vZ, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp <;> field_simp

/-- Step B: normalise `c0` to `(1,1,1)` by a diagonal map and the last three vectors to
affine representatives `(a,b,1),(c,1,d),(1,e,f)`. -/
def eqvB : {c : Fin 4 → Fin 3 → F // Good7 (stdA c)} ≃
    (Fin 3 → Fˣ) × (Fin 3 → Fˣ) × {t : T6 F // NG t} where
  toFun c := (dOf c.2, sOf c.2, ⟨tOf c.1, (good_cB _ _ _).1 (by rw [recon_B c.2]; exact c.2)⟩)
  invFun p := ⟨cB p.1 p.2.1 p.2.2.1, (good_cB _ _ _).2 p.2.2.2⟩
  left_inv c := Subtype.ext (recon_B c.2)
  right_inv p := by
    obtain ⟨d, s, t, ht⟩ := p
    exact Prod.ext (dOf_cB d s t ((good_cB d s t).2 ht))
      (Prod.ext (sOf_cB d s t ((good_cB d s t).2 ht)) (Subtype.ext (tOf_cB d s t)))

/-- **Frame normalisation of the actual Δ7 count.** -/
theorem indepCount_Δ7_frame [Fintype F] :
    indepCount (F := F) Lift.Δ7 3 =
      (∏ i : Fin 3, (Fintype.card F ^ 3 - Fintype.card F ^ (i : ℕ))) *
        ((Fintype.card F - 1) ^ 3 * ((Fintype.card F - 1) ^ 3 * Nat.card {t : T6 F // NG t})) := by
  rw [indepCount_Δ7, Nat.card_congr eqvA, Nat.card_prod, card_bases, Nat.card_congr eqvB,
    Nat.card_prod, Nat.card_prod, Nat.card_fun, Nat.card_units, Nat.card_eq_fintype_card (α := F),
    Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]

end Count
end QArr372486

#print axioms QArr372486.Count.indepCount_Δ7_frame
#print axioms QArr372486.Count.good7_nrmT
#print axioms QArr372486.Count.li_iff_det
```

## QArr372486Affine.lean

```lean
import QArr372486Frame
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

/-! MathDB 372486 (Opus lane, credit 0): exact count of
`N6 = #{(a,b,c,d,e,f) | a≠b, c≠d, e≠f, Dx ≠ 0}` over every finite field. -/

noncomputable section
open Finset

namespace QArr372486
namespace Count

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Integer indicator. -/
def ind (p : Prop) [Decidable p] : ℤ := if p then 1 else 0

theorem ind_and (p r : Prop) [Decidable p] [Decidable r] : ind (p ∧ r) = ind p * ind r := by
  unfold ind
  by_cases hp : p <;> by_cases hr : r <;> simp [hp, hr]

theorem ind_not (p : Prop) [Decidable p] : ind (¬p) = 1 - ind p := by
  unfold ind
  by_cases hp : p <;> simp [hp]

theorem sum_lin (α β : F) : (∑ x : F, ind (α * x + β = 0)) =
    if α = 0 then (if β = 0 then (Fintype.card F : ℤ) else 0) else 1 := by
  by_cases hα : α = 0
  · subst hα
    by_cases hβ : β = 0 <;> simp [ind, hβ]
  · have key : ∀ x, α * x + β = 0 ↔ x = -β / α := by
      intro x
      rw [eq_div_iff hα]
      constructor <;> intro h <;> linear_combination h
    simp [ind, key, hα]

omit [Field F] in
theorem sum_ne_mul (b : F) (g : F → ℤ) :
    (∑ x : F, ind (x ≠ b) * g x) = (∑ x : F, g x) - g b := by
  have h : ∀ x, ind (x ≠ b) * g x = g x - (if x = b then g b else 0) := by
    intro x
    by_cases hx : x = b
    · subst hx; simp [ind]
    · simp [ind, hx]
  rw [sum_congr rfl fun x _ => h x, sum_sub_distrib]
  simp

omit [Field F] in
theorem sum_ind_ne (b : F) : (∑ x : F, ind (x ≠ b)) = (Fintype.card F : ℤ) - 1 := by
  have := sum_ne_mul b (fun _ => (1 : ℤ))
  simp only [mul_one] at this
  rw [this]
  simp

/-- Inner count over `(e,f)` of `e ≠ f` and `n0 + n1 e + n2 f = 0`. -/
def Gval (n0 n1 n2 : F) : ℤ :=
  ((Fintype.card F : ℤ) - 1) - ((Fintype.card F : ℤ) - 1) * ind (n1 + n2 = 0) +
    (Fintype.card F : ℤ) * (ind (n1 + n2 = 0) * ind (n1 ≠ 0) * ind (n0 ≠ 0)) +
    (Fintype.card F : ℤ) * ((Fintype.card F : ℤ) - 1) *
      (ind (n1 + n2 = 0) * ind (n1 = 0) * ind (n0 = 0))

theorem G_eq (n0 n1 n2 : F) :
    (∑ e : F, ∑ f : F, ind (e ≠ f) * ind (n0 + n1 * e + n2 * f = 0)) = Gval n0 n1 n2 := by
  rw [Finset.sum_comm]
  have h1 : ∀ f : F, (∑ e : F, ind (e ≠ f) * ind (n0 + n1 * e + n2 * f = 0)) =
      (∑ e : F, ind (n1 * e + (n0 + n2 * f) = 0)) - ind ((n1 + n2) * f + n0 = 0) := by
    intro f
    rw [sum_ne_mul f (fun e => ind (n0 + n1 * e + n2 * f = 0))]
    congr 1
    · refine sum_congr rfl fun e _ => ?_
      rw [show n0 + n1 * e + n2 * f = n1 * e + (n0 + n2 * f) by ring]
    · rw [show n0 + n1 * f + n2 * f = (n1 + n2) * f + n0 by ring]
  by_cases hn1 : n1 = 0
  · subst hn1
    have h1' : ∀ f : F, (∑ e : F, ind (e ≠ f) * ind (n0 + 0 * e + n2 * f = 0)) =
        ((Fintype.card F : ℤ) - 1) * ind (n2 * f + n0 = 0) := by
      intro f
      rw [sum_ne_mul f (fun e => ind (n0 + 0 * e + n2 * f = 0))]
      simp only [zero_mul, add_zero]
      by_cases hf : n2 * f + n0 = 0
      · have hf' : n0 + n2 * f = 0 := by rw [add_comm]; exact hf
        simp [ind, hf, hf']
      · have hf' : ¬ n0 + n2 * f = 0 := by rw [add_comm]; exact hf
        simp [ind, hf, hf']
    simp only [h1', ← Finset.mul_sum, sum_lin, Gval]
    by_cases hs : n2 = 0 <;> by_cases h0 : n0 = 0 <;> simp [ind, hs, h0]
    all_goals ring
  · have h2 : ∀ f : F, (∑ e : F, ind (e ≠ f) * ind (n0 + n1 * e + n2 * f = 0)) =
        1 - ind ((n1 + n2) * f + n0 = 0) := by
      intro f
      rw [h1 f, sum_lin]
      simp [hn1]
    simp only [h2, Finset.sum_sub_distrib, sum_lin, Gval]
    by_cases hs : n1 + n2 = 0 <;> by_cases h0 : n0 = 0 <;> simp [ind, hs, h0, hn1]

omit [Field F] in
theorem ind_eq_iff {p r : Prop} [Decidable p] [Decidable r] (h : p ↔ r) : ind p = ind r := by
  unfold ind; by_cases hp : p <;> simp [hp, h.mp] <;> simp_all

omit [Field F] in
theorem sum_mul_ind_eq (v : F) (g : F → ℤ) : (∑ x : F, g x * ind (x = v)) = g v := by
  simp [ind]

theorem sum_ind_bd (b : F) (h : F → ℤ) :
    (∑ d : F, ind (b * d - 1 = 0) * h d) = if b = 0 then 0 else h b⁻¹ := by
  by_cases hb : b = 0
  · subst hb; simp [ind]
  · have key : ∀ d, b * d - 1 = 0 ↔ d = b⁻¹ := by
      intro d
      rw [sub_eq_zero]
      constructor
      · exact eq_inv_of_mul_eq_one_right
      · intro h; rw [h, mul_inv_cancel₀ hb]
    simp [ind, key, hb]

/-- `ξ(b,d) = #{a≠b, c≠d, s = 0, c = a d}`. -/
def xi (b d : F) : ℤ := ∑ a : F, ∑ c : F, ind (a ≠ b) * ind (c ≠ d) *
  (ind (c * (1 - b) + a * (1 - d) = 0) * ind (c - a * d = 0))

/-- `σ(b,d) = #{a≠b, c≠d, s = 0}`. -/
def sgm (b d : F) : ℤ := ∑ a : F, ∑ c : F, ind (a ≠ b) * ind (c ≠ d) *
  ind (c * (1 - b) + a * (1 - d) = 0)

theorem xi_red (b d : F) : xi b d =
    ∑ a : F, ind (a ≠ b) * ind (a * d ≠ d) * ind (a * (1 - b * d) = 0) := by
  unfold xi
  refine sum_congr rfl fun a _ => ?_
  have h : ∀ c, ind (a ≠ b) * ind (c ≠ d) * (ind (c * (1 - b) + a * (1 - d) = 0) *
      ind (c - a * d = 0)) = (ind (a ≠ b) * ind (c ≠ d) * ind (c * (1 - b) + a * (1 - d) = 0)) *
      ind (c = a * d) := by
    intro c
    rw [ind_eq_iff sub_eq_zero]
    ring
  rw [sum_congr rfl fun c _ => h c, sum_mul_ind_eq]
  rw [show a * d * (1 - b) + a * (1 - d) = a * (1 - b * d) by ring]

theorem mul_d_ne {a d : F} (hd : d ≠ 0) : ind (a * d ≠ d) = ind (a ≠ 1) :=
  ind_eq_iff (not_congr ⟨fun h => mul_right_cancel₀ hd (by rw [h, one_mul]),
    fun h => by rw [h, one_mul]⟩)

theorem sum_ne_b_ne_one (b : F) :
    (∑ a : F, ind (a ≠ b) * ind (a ≠ 1)) = ((Fintype.card F : ℤ) - 1) - ind (b ≠ 1) := by
  rw [sum_ne_mul b (fun a => ind (a ≠ 1)), sum_ind_ne]

theorem xi_closed (b d : F) : xi b d =
    ind (b * d - 1 = 0) * (((Fintype.card F : ℤ) - 1) - ind (b ≠ 1)) +
      (1 - ind (b * d - 1 = 0)) * (ind (b ≠ 0) * ind (d ≠ 0)) := by
  rw [xi_red]
  by_cases hbd : b * d - 1 = 0
  · have hd : d ≠ 0 := by rintro rfl; simp at hbd
    have h1 : 1 - b * d = 0 := by linear_combination -hbd
    have hpt : ∀ a : F, ind (a ≠ b) * ind (a * d ≠ d) * ind (a * (1 - b * d) = 0) =
        ind (a ≠ b) * ind (a ≠ 1) := by
      intro a
      rw [mul_d_ne hd, h1, mul_zero]
      simp [ind]
    rw [sum_congr rfl fun a _ => hpt a, sum_ne_b_ne_one]
    simp [ind, hbd]
  · have h1 : 1 - b * d ≠ 0 := fun h => hbd (by linear_combination -h)
    have hpt : ∀ a : F, ind (a ≠ b) * ind (a * d ≠ d) * ind (a * (1 - b * d) = 0) =
        ind (a ≠ b) * ind (a * d ≠ d) * ind (a = 0) := by
      intro a
      rw [ind_eq_iff (show a * (1 - b * d) = 0 ↔ a = 0 by simp [h1])]
    rw [sum_congr rfl fun a _ => hpt a, sum_mul_ind_eq (0 : F) (fun a => ind (a ≠ b) * ind (a * d ≠ d)),
      ind_eq_iff (ne_comm : (0 : F) ≠ b ↔ b ≠ 0),
      ind_eq_iff (show (0 : F) * d ≠ d ↔ d ≠ 0 by rw [zero_mul]; exact ne_comm)]
    simp [ind, hbd]

theorem sum_ite_pt (v : F) (X Y : ℤ) :
    (∑ b : F, if b = v then X else Y) = X + ((Fintype.card F : ℤ) - 1) * Y := by
  have h : ∀ b : F, (if b = v then X else Y) = Y + (X - Y) * ind (b = v) := by
    intro b
    by_cases hb : b = v <;> simp [ind, hb]
  rw [sum_congr rfl fun b _ => h b, sum_add_distrib, ← mul_sum]
  simp [ind]
  ring

theorem sgm_bd1 (b d : F) (h : b * d - 1 = 0) :
    sgm b d = if b = 1 then ((Fintype.card F : ℤ) - 1) ^ 2 else (Fintype.card F : ℤ) - 2 := by
  unfold sgm
  have hd : d ≠ 0 := by rintro rfl; simp at h
  by_cases hb : b = 1
  · subst hb
    have hd1 : d = 1 := by linear_combination h
    subst hd1
    have hS : ∀ a c : F, ind (c * (1 - 1) + a * (1 - 1) = 0) = 1 := by intro a c; simp [ind]
    have hr : (if (1 : F) = 1 then ((Fintype.card F : ℤ) - 1) ^ 2 else (Fintype.card F : ℤ) - 2)
        = ((Fintype.card F : ℤ) - 1) ^ 2 := by simp
    simp only [hS, mul_one, hr]
    rw [← Finset.sum_mul_sum, sum_ind_ne]
    simp only [↓reduceIte]
    ring
  · have hs : ∀ a c : F, ind (c * (1 - b) + a * (1 - d) = 0) = ind (c = a * d) := by
      intro a c
      have hb' : 1 - b ≠ 0 := fun h' => hb (by linear_combination -h')
      refine ind_eq_iff ?_
      rw [show c * (1 - b) + a * (1 - d) = (1 - b) * (c - a * d) by linear_combination (-a) * h]
      simp [hb', sub_eq_zero]
    have hpt : ∀ a : F, (∑ c : F, ind (a ≠ b) * ind (c ≠ d) * ind (c * (1 - b) + a * (1 - d) = 0))
        = ind (a ≠ b) * ind (a ≠ 1) := by
      intro a
      simp only [hs]
      rw [sum_mul_ind_eq (a * d) (fun c => ind (a ≠ b) * ind (c ≠ d)), mul_d_ne hd]
    rw [sum_congr rfl fun a _ => hpt a, sum_ne_b_ne_one]
    simp [ind, hb]
    ring

theorem B_val : (∑ b : F, ∑ d : F, ind (b * d - 1 = 0) * xi b d) =
    (Fintype.card F : ℤ) ^ 2 - 3 * (Fintype.card F : ℤ) + 3 := by
  have hpt : ∀ b d : F, ind (b * d - 1 = 0) * xi b d =
      ind (b * d - 1 = 0) * (((Fintype.card F : ℤ) - 1) - ind (b ≠ 1)) := by
    intro b d
    rw [xi_closed]
    by_cases h : b * d - 1 = 0 <;> simp [ind, h]
  simp only [hpt, sum_ind_bd]
  have h2 : ∀ b : F, (if b = 0 then (0 : ℤ) else ((Fintype.card F : ℤ) - 1) - ind (b ≠ 1)) =
      ind (b ≠ 0) * (((Fintype.card F : ℤ) - 1) - ind (b ≠ 1)) := by
    intro b
    by_cases hb : b = 0 <;> simp [ind, hb]
  simp only [h2]
  rw [sum_ne_mul (0 : F), sum_sub_distrib, sum_ind_ne]
  simp [ind]
  ring

theorem sum_ind_bd_one (b : F) : (∑ d : F, ind (b * d - 1 = 0)) = if b = 0 then 0 else 1 := by
  have := sum_ind_bd b (fun _ => (1 : ℤ))
  simpa using this

theorem X_val : (∑ b : F, ∑ d : F, xi b d) =
    2 * (Fintype.card F : ℤ) ^ 2 - 6 * (Fintype.card F : ℤ) + 5 := by
  have hpt : ∀ b d : F, xi b d = ind (b * d - 1 = 0) * xi b d +
      (ind (b ≠ 0) * ind (d ≠ 0) - ind (b * d - 1 = 0)) := by
    intro b d
    rw [xi_closed]
    by_cases h : b * d - 1 = 0
    · have hb : b ≠ 0 := by rintro rfl; simp at h
      have hd : d ≠ 0 := by rintro rfl; simp at h
      simp [ind, h, hb, hd]
    · simp [ind, h]
  rw [sum_congr rfl fun b _ => sum_congr rfl fun d _ => hpt b d]
  simp only [sum_add_distrib, sum_sub_distrib]
  rw [B_val, ← Finset.sum_mul_sum, sum_ind_ne]
  simp only [sum_ind_bd_one]
  rw [show (∑ b : F, if b = 0 then (0 : ℤ) else 1) = 0 + ((Fintype.card F : ℤ) - 1) * 1 from
    sum_ite_pt 0 0 1]
  ring

theorem A_val : (∑ b : F, ∑ d : F, ind (b * d - 1 = 0) * sgm b d) =
    ((Fintype.card F : ℤ) - 1) ^ 2 + ((Fintype.card F : ℤ) - 2) ^ 2 := by
  simp only [sum_ind_bd]
  have hpt : ∀ b : F, (if b = 0 then (0 : ℤ) else sgm b b⁻¹) =
      (if b = 1 then ((Fintype.card F : ℤ) - 1) ^ 2 else (Fintype.card F : ℤ) - 2) -
        (if b = 0 then (Fintype.card F : ℤ) - 2 else 0) := by
    intro b
    by_cases hb : b = 0
    · subst hb; simp
    · simp only [hb, ↓reduceIte]
      rw [sgm_bd1 b b⁻¹ (by rw [mul_inv_cancel₀ hb, sub_self])]
      simp [hb]
  rw [sum_congr rfl fun b _ => hpt b, sum_sub_distrib, sum_ite_pt]
  simp
  ring

omit [Field F] in
theorem sum_ind_eq_mul (b : F) (g : F → ℤ) : (∑ a : F, ind (a = b) * g a) = g b := by
  simp [ind]

theorem sum_L2 (α β : F) : (∑ a : F, ∑ c : F, ind (c * α + a * β = 0)) =
    if α = 0 ∧ β = 0 then (Fintype.card F : ℤ) ^ 2 else (Fintype.card F : ℤ) := by
  by_cases hα : α = 0
  · subst hα
    have h1 : ∀ a c : F, ind (c * 0 + a * β = 0) = ind (β * a + 0 = 0) :=
      fun a c => ind_eq_iff (by rw [mul_zero, zero_add, add_zero, mul_comm])
    simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.mul_sum, sum_lin]
    by_cases hβ : β = 0 <;> simp [hβ]
    ring
  · have h1 : ∀ a : F, (∑ c : F, ind (c * α + a * β = 0)) = 1 := by
      intro a
      have := sum_lin α (a * β)
      simp only [hα, ↓reduceIte] at this
      rw [← this]
      exact sum_congr rfl fun c _ => ind_eq_iff (by rw [mul_comm])
    simp [h1, hα]

/-- `κ0 = #{(b,d) | d(1-b) + b(1-d) = 0}`. -/
def kap (F : Type*) [Field F] [Fintype F] [DecidableEq F] : ℤ :=
  ∑ b : F, ∑ d : F, ind (d * (1 - b) + b * (1 - d) = 0)

theorem kap_row (b : F) : (∑ d : F, ind (d * (1 - b) + b * (1 - d) = 0)) =
    if 1 - 2 * b = 0 then (if b = 0 then (Fintype.card F : ℤ) else 0) else 1 := by
  rw [← sum_lin]
  exact sum_congr rfl fun d _ => ind_eq_iff (by constructor <;> intro h <;> linear_combination h)

theorem kap_odd (h2 : (2 : F) ≠ 0) : kap F = (Fintype.card F : ℤ) - 1 := by
  unfold kap
  simp only [kap_row]
  have hpt : ∀ b : F, (if 1 - 2 * b = 0 then (if b = 0 then (Fintype.card F : ℤ) else 0) else 1) =
      1 - ind ((-2) * b + 1 = 0) := by
    intro b
    by_cases hb : 1 - 2 * b = 0
    · have hb0 : b ≠ 0 := by rintro rfl; simp at hb
      have : (-2) * b + 1 = 0 := by linear_combination hb
      simp only [ind, hb, hb0, this, ↓reduceIte, sub_self]
    · have : ¬ (-2) * b + 1 = 0 := fun h => hb (by linear_combination h)
      simp only [ind, hb, this, ↓reduceIte, sub_zero]
  rw [sum_congr rfl fun b _ => hpt b, sum_sub_distrib, sum_lin]
  have : (-2 : F) ≠ 0 := neg_ne_zero.2 h2
  simp [this]

theorem kap_even (h2 : (2 : F) = 0) : kap F = (Fintype.card F : ℤ) := by
  unfold kap
  simp only [kap_row]
  have hpt : ∀ b : F, 1 - 2 * b ≠ 0 := by
    intro b; rw [h2, zero_mul, sub_zero]; exact one_ne_zero
  simp [hpt]

theorem ind_ne (x y : F) : ind (x ≠ y) = 1 - ind (x = y) := ind_not _

theorem T0 : (∑ b : F, ∑ d : F, ∑ a : F, ∑ c : F, ind (c * (1 - b) + a * (1 - d) = 0)) =
    (Fintype.card F : ℤ) ^ 3 + (Fintype.card F : ℤ) ^ 2 - (Fintype.card F : ℤ) := by
  simp only [sum_L2]
  have hpt : ∀ b d : F, (if 1 - b = 0 ∧ 1 - d = 0 then (Fintype.card F : ℤ) ^ 2
      else (Fintype.card F : ℤ)) = (Fintype.card F : ℤ) +
        ((Fintype.card F : ℤ) ^ 2 - (Fintype.card F : ℤ)) * (ind (b = 1) * ind (d = 1)) := by
    intro b d
    have e1 : ∀ x : F, (1 - x = 0) ↔ (x = 1) := fun x => by rw [sub_eq_zero, eq_comm]
    simp only [e1]
    by_cases hb : b = 1 <;> by_cases hd : d = 1 <;> simp [ind, hb, hd]
  rw [sum_congr rfl fun b _ => sum_congr rfl fun d _ => hpt b d]
  simp only [sum_add_distrib, ← Finset.mul_sum]
  simp [ind]
  ring

theorem T1 : (∑ b : F, ∑ d : F, ∑ a : F, ∑ c : F,
    ind (a = b) * ind (c * (1 - b) + a * (1 - d) = 0)) = (Fintype.card F : ℤ) ^ 2 := by
  have per : ∀ b d : F, (∑ a : F, ∑ c : F, ind (a = b) * ind (c * (1 - b) + a * (1 - d) = 0)) =
      if b = 1 then (Fintype.card F : ℤ) * ind (d = 1) else 1 := by
    intro b d
    simp only [← Finset.mul_sum]
    rw [sum_ind_eq_mul b (fun a => ∑ c : F, ind (c * (1 - b) + a * (1 - d) = 0))]
    rw [show (∑ c : F, ind (c * (1 - b) + b * (1 - d) = 0)) =
        ∑ c : F, ind ((1 - b) * c + b * (1 - d) = 0) from
      sum_congr rfl fun c _ => ind_eq_iff (by rw [mul_comm]), sum_lin]
    by_cases hb : b = 1
    · subst hb
      by_cases hd : d = 1
      · subst hd; simp [ind]
      · simp [ind, hd, sub_eq_zero, Ne.symm hd]
    · have : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb)
      simp [hb, this]
  rw [sum_congr rfl fun b _ => sum_congr rfl fun d _ => per b d]
  have row : ∀ b : F, (∑ d : F, if b = 1 then (Fintype.card F : ℤ) * ind (d = 1) else 1) =
      (Fintype.card F : ℤ) := by
    intro b
    by_cases hb : b = 1 <;> simp [hb, ind]
  simp only [row]
  simp
  ring

theorem T2 : (∑ b : F, ∑ d : F, ∑ a : F, ∑ c : F,
    ind (c = d) * ind (c * (1 - b) + a * (1 - d) = 0)) = (Fintype.card F : ℤ) ^ 2 := by
  have per : ∀ b d : F, (∑ a : F, ∑ c : F, ind (c = d) * ind (c * (1 - b) + a * (1 - d) = 0)) =
      if d = 1 then (Fintype.card F : ℤ) * ind (b = 1) else 1 := by
    intro b d
    have hc : ∀ a : F, (∑ c : F, ind (c = d) * ind (c * (1 - b) + a * (1 - d) = 0)) =
        ind ((1 - d) * a + d * (1 - b) = 0) := by
      intro a
      rw [sum_ind_eq_mul d (fun c => ind (c * (1 - b) + a * (1 - d) = 0))]
      exact ind_eq_iff (by constructor <;> intro h <;> linear_combination h)
    simp only [hc, sum_lin]
    by_cases hd : d = 1
    · subst hd
      by_cases hb : b = 1
      · subst hb; simp [ind]
      · simp [ind, hb, sub_eq_zero, Ne.symm hb]
    · have : 1 - d ≠ 0 := sub_ne_zero.2 (Ne.symm hd)
      simp [hd, this]
  rw [sum_congr rfl fun b _ => sum_congr rfl fun d _ => per b d]
  simp only [sum_ite_pt, sum_add_distrib, ← Finset.mul_sum]
  simp [ind]
  ring

theorem T3 : (∑ b : F, ∑ d : F, ∑ a : F, ∑ c : F,
    ind (a = b) * ind (c = d) * ind (c * (1 - b) + a * (1 - d) = 0)) = kap F := by
  unfold kap
  refine sum_congr rfl fun b _ => sum_congr rfl fun d _ => ?_
  have h1 : ∀ a : F, (∑ c : F, ind (a = b) * ind (c = d) * ind (c * (1 - b) + a * (1 - d) = 0)) =
      ind (a = b) * ind (d * (1 - b) + a * (1 - d) = 0) := by
    intro a
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [sum_ind_eq_mul d (fun c => ind (c * (1 - b) + a * (1 - d) = 0))]
  simp only [h1]
  exact sum_ind_eq_mul b (fun a => ind (d * (1 - b) + a * (1 - d) = 0))

theorem sig_val : (∑ b : F, ∑ d : F, sgm b d) =
    (Fintype.card F : ℤ) ^ 3 - (Fintype.card F : ℤ) ^ 2 - (Fintype.card F : ℤ) + kap F := by
  unfold sgm
  have hpt : ∀ a b c d : F, ind (a ≠ b) * ind (c ≠ d) * ind (c * (1 - b) + a * (1 - d) = 0) =
      ind (c * (1 - b) + a * (1 - d) = 0) - ind (a = b) * ind (c * (1 - b) + a * (1 - d) = 0) -
        ind (c = d) * ind (c * (1 - b) + a * (1 - d) = 0) +
        ind (a = b) * ind (c = d) * ind (c * (1 - b) + a * (1 - d) = 0) := by
    intro a b c d
    rw [ind_ne, ind_ne]
    ring
  simp only [hpt, sum_add_distrib, sum_sub_distrib]
  rw [T0, T1, T2, T3]
  ring

instance decNG (t : T6 F) : Decidable (NG t) := by unfold NG; infer_instance

theorem ng_ind (a b c d e f : F) : ind (NG (a, b, c, d, e, f)) =
    ind (a ≠ b) * ind (c ≠ d) * (ind (e ≠ f) - ind (e ≠ f) *
      ind ((b * d - 1) + (c - a * d) * e + (a - b * c) * f = 0)) := by
  rw [ind_eq_iff (show NG (a, b, c, d, e, f) ↔ (a ≠ b ∧ c ≠ d) ∧
      (e ≠ f ∧ ¬ ((b * d - 1) + (c - a * d) * e + (a - b * c) * f = 0)) from by
    show (a ≠ b ∧ c ≠ d ∧ e ≠ f ∧ Dx a b c d e f ≠ 0) ↔ _
    unfold Dx
    tauto)]
  rw [ind_and, ind_and, ind_and,
    ind_not ((b * d - 1) + (c - a * d) * e + (a - b * c) * f = 0)]
  ring

theorem inner_eq (b d : F) :
    (∑ a : F, ∑ c : F, ∑ e : F, ∑ f : F, ind (NG (a, b, c, d, e, f))) =
      ((Fintype.card F : ℤ) - 1) ^ 4 +
        (((Fintype.card F : ℤ) - 1) - (Fintype.card F : ℤ) * (1 - ind (b * d - 1 = 0))) * sgm b d +
        ((Fintype.card F : ℤ) * (1 - ind (b * d - 1 = 0)) -
          (Fintype.card F : ℤ) * ((Fintype.card F : ℤ) - 1) * ind (b * d - 1 = 0)) * xi b d := by
  have hef : (∑ e : F, ∑ f : F, ind (e ≠ f)) = (Fintype.card F : ℤ) * ((Fintype.card F : ℤ) - 1) := by
    rw [Finset.sum_comm]
    simp only [sum_ind_ne]
    simp
    ring
  have hpt : ∀ a c : F, (∑ e : F, ∑ f : F, ind (NG (a, b, c, d, e, f))) =
      ((Fintype.card F : ℤ) - 1) ^ 2 * (ind (a ≠ b) * ind (c ≠ d)) +
      (((Fintype.card F : ℤ) - 1) - (Fintype.card F : ℤ) * (1 - ind (b * d - 1 = 0))) *
        (ind (a ≠ b) * ind (c ≠ d) * ind (c * (1 - b) + a * (1 - d) = 0)) +
      ((Fintype.card F : ℤ) * (1 - ind (b * d - 1 = 0)) -
          (Fintype.card F : ℤ) * ((Fintype.card F : ℤ) - 1) * ind (b * d - 1 = 0)) *
        (ind (a ≠ b) * ind (c ≠ d) *
          (ind (c * (1 - b) + a * (1 - d) = 0) * ind (c - a * d = 0))) := by
    intro a c
    simp only [ng_ind, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hef, G_eq]
    unfold Gval
    rw [ind_eq_iff (show (c - a * d) + (a - b * c) = 0 ↔ c * (1 - b) + a * (1 - d) = 0 by
      constructor <;> intro h <;> linear_combination h), ind_ne (c - a * d) 0, ind_ne (b * d - 1) 0]
    ring
  rw [sum_congr rfl fun a _ => sum_congr rfl fun c _ => hpt a c]
  unfold sgm xi
  simp only [sum_add_distrib, ← Finset.mul_sum]
  rw [← Finset.sum_mul, sum_ind_ne, sum_ind_ne]
  ring

omit [Field F] [DecidableEq F] in
theorem reorder (φ : F → F → F → F → ℤ) :
    (∑ a : F, ∑ b : F, ∑ c : F, ∑ d : F, φ a b c d) = ∑ b : F, ∑ d : F, ∑ a : F, ∑ c : F, φ a b c d := by
  calc (∑ a : F, ∑ b : F, ∑ c : F, ∑ d : F, φ a b c d)
      = ∑ b : F, ∑ a : F, ∑ c : F, ∑ d : F, φ a b c d := Finset.sum_comm
    _ = ∑ b : F, ∑ d : F, ∑ a : F, ∑ c : F, φ a b c d := by
      refine sum_congr rfl fun b _ => ?_
      calc (∑ a : F, ∑ c : F, ∑ d : F, φ a b c d) = ∑ a : F, ∑ d : F, ∑ c : F, φ a b c d :=
            sum_congr rfl fun a _ => Finset.sum_comm
        _ = ∑ d : F, ∑ a : F, ∑ c : F, φ a b c d := Finset.sum_comm

/-- **Exact affine count over every finite field.** -/
theorem N6_val : (Nat.card {t : T6 F // NG t} : ℤ) =
    (Fintype.card F : ℤ) ^ 6 - 4 * (Fintype.card F : ℤ) ^ 5 + 5 * (Fintype.card F : ℤ) ^ 4 +
      2 * (Fintype.card F : ℤ) ^ 3 - 13 * (Fintype.card F : ℤ) ^ 2 + 11 * (Fintype.card F : ℤ)
      - kap F := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  push_cast
  have h1 : (∑ t : T6 F, (if NG t then (1 : ℤ) else 0)) =
      ∑ a : F, ∑ b : F, ∑ c : F, ∑ d : F, ∑ e : F, ∑ f : F, ind (NG (a, b, c, d, e, f)) := by
    simp only [Fintype.sum_prod_type]
    rfl
  rw [h1, reorder (fun a b c d => ∑ e : F, ∑ f : F, ind (NG (a, b, c, d, e, f)))]
  simp only [inner_eq]
  have hpt : ∀ b d : F, ((Fintype.card F : ℤ) - 1) ^ 4 +
      (((Fintype.card F : ℤ) - 1) - (Fintype.card F : ℤ) * (1 - ind (b * d - 1 = 0))) * sgm b d +
      ((Fintype.card F : ℤ) * (1 - ind (b * d - 1 = 0)) -
        (Fintype.card F : ℤ) * ((Fintype.card F : ℤ) - 1) * ind (b * d - 1 = 0)) * xi b d =
      ((Fintype.card F : ℤ) - 1) ^ 4 - sgm b d + (Fintype.card F : ℤ) * (ind (b * d - 1 = 0) * sgm b d)
        + (Fintype.card F : ℤ) * xi b d
        - (Fintype.card F : ℤ) ^ 2 * (ind (b * d - 1 = 0) * xi b d) := by
    intro b d; ring
  simp only [hpt, sum_add_distrib, sum_sub_distrib, ← Finset.mul_sum]
  rw [sig_val, A_val, X_val, B_val]
  simp
  ring

end Count
end QArr372486

#print axioms QArr372486.Count.N6_val
#print axioms QArr372486.Count.kap_odd
#print axioms QArr372486.Count.kap_even
```

## QArr372486ProjCount.lean

```lean
import QArr372486Affine
import Mathlib.Algebra.Field.ZMod

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

/-! MathDB 372486 (Opus lane, credit 0): exact `indepCount Δ7 3` for the actual seven-label
complex `Lift.Δ7` over every finite field, specialised to odd fields and to `ZMod 2`. -/

noncomputable section
open Finset

namespace QArr372486
namespace Count

/-- `P(q) = q^6-4q^5+5q^4+2q^3-13q^2+10q+1`. -/
def Pq (q : ℤ) : ℤ := q ^ 6 - 4 * q ^ 5 + 5 * q ^ 4 + 2 * q ^ 3 - 13 * q ^ 2 + 10 * q + 1

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem prod_GL3 : (∏ i : Fin 3, (Fintype.card F ^ 3 - Fintype.card F ^ (i : ℕ)) : ℕ) =
    (Fintype.card F ^ 3 - 1) * (Fintype.card F ^ 3 - Fintype.card F) *
      (Fintype.card F ^ 3 - Fintype.card F ^ 2) := by
  rw [Fin.prod_univ_three]
  simp

/-- **All finite fields.** -/
theorem indepCount_Δ7_all :
    (indepCount (F := F) Lift.Δ7 3 : ℤ) =
      ((Fintype.card F : ℤ) - 1) ^ 7 * (Fintype.card F : ℤ) ^ 3 * ((Fintype.card F : ℤ) ^ 3 - 1) *
        ((Fintype.card F : ℤ) ^ 2 - 1) *
          (Pq (Fintype.card F) + ((Fintype.card F : ℤ) - 1) - kap F) := by
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  have h1 : 1 ≤ Fintype.card F ^ 3 := Nat.one_le_pow _ _ hq
  have h2 : Fintype.card F ≤ Fintype.card F ^ 3 := by
    calc Fintype.card F = Fintype.card F ^ 1 := (pow_one _).symm
      _ ≤ Fintype.card F ^ 3 := Nat.pow_le_pow_right hq (by norm_num)
  have h3 : Fintype.card F ^ 2 ≤ Fintype.card F ^ 3 := Nat.pow_le_pow_right hq (by norm_num)
  rw [indepCount_Δ7_frame, prod_GL3]
  push_cast [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3, Nat.cast_sub hq]
  rw [N6_val]
  unfold Pq
  ring

/-- **Odd characteristic** (`2 ≠ 0`): `(q-1)^7 q^3 (q^3-1)(q^2-1) P(q)`. -/
theorem indepCount_Δ7_odd (h2 : (2 : F) ≠ 0) :
    (indepCount (F := F) Lift.Δ7 3 : ℤ) =
      ((Fintype.card F : ℤ) - 1) ^ 7 * (Fintype.card F : ℤ) ^ 3 * ((Fintype.card F : ℤ) ^ 3 - 1) *
        ((Fintype.card F : ℤ) ^ 2 - 1) * Pq (Fintype.card F) := by
  rw [indepCount_Δ7_all, kap_odd h2]
  ring

/-- **Characteristic two**: `(q-1)^7 q^3 (q^3-1)(q^2-1) (P(q) - 1)`. -/
theorem indepCount_Δ7_even (h2 : (2 : F) = 0) :
    (indepCount (F := F) Lift.Δ7 3 : ℤ) =
      ((Fintype.card F : ℤ) - 1) ^ 7 * (Fintype.card F : ℤ) ^ 3 * ((Fintype.card F : ℤ) ^ 3 - 1) *
        ((Fintype.card F : ℤ) ^ 2 - 1) * (Pq (Fintype.card F) - 1) := by
  rw [indepCount_Δ7_all, kap_even h2]
  ring

/-- **`F₂`**: the actual count vanishes. -/
theorem indepCount_Δ7_F2 : indepCount (F := ZMod 2) Lift.Δ7 3 = 0 := by
  have h := indepCount_Δ7_even (F := ZMod 2) (by decide)
  rw [ZMod.card] at h
  unfold Pq at h
  norm_num at h
  exact_mod_cast h

theorem two_ne_zero_zmod (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have hle := Nat.le_of_dvd (by norm_num) h'
  have hge := (Fact.out : p.Prime).two_le
  exact hp (by omega)

/-- **Odd primes** `ZMod p`. -/
theorem indepCount_Δ7_zmod (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (indepCount (F := ZMod p) Lift.Δ7 3 : ℤ) =
      ((p : ℤ) - 1) ^ 7 * (p : ℤ) ^ 3 * ((p : ℤ) ^ 3 - 1) * ((p : ℤ) ^ 2 - 1) * Pq p := by
  have h := indepCount_Δ7_odd (F := ZMod p) (two_ne_zero_zmod p hp)
  rwa [ZMod.card] at h

end Count
end QArr372486

#print axioms QArr372486.Count.indepCount_Δ7_all
#print axioms QArr372486.Count.indepCount_Δ7_odd
#print axioms QArr372486.Count.indepCount_Δ7_even
#print axioms QArr372486.Count.indepCount_Δ7_F2
#print axioms QArr372486.Count.indepCount_Δ7_zmod
```

## QArr372486Refute.lean

```lean
import QArr372486ProjCount
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.PrimeFin

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-! MathDB 372486 (Opus lane, credit 0): failure of NTUY polynomiality (Conj. 2.6 (P)) for an
explicit graph family on `Fin 33`, hence failure of the native conjunction. -/

noncomputable section
open Finset Polynomial

namespace QArr372486
namespace Refute

/-- (P) on prime fields: one `Q ∈ ℂ[q][t]` with `χ(A_G^{F_p}, t) = Q(p, t)` for every prime `p`. -/
def PolyPrime {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ Q : Polynomial (Polynomial ℂ), ∀ (p : ℕ) [Fact p.Prime],
    (charPoly (graphArr (F := ZMod p) G)).map (Int.castRingHom ℂ) =
      Q.map (Polynomial.evalRingHom (p : ℂ))

/-- (P) literally over all finite fields `F` (all prime powers `q = |F|`). -/
def PolyAll {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ Q : Polynomial (Polynomial ℂ), ∀ (F : Type) [Field F] [Fintype F],
    (charPoly (graphArr (F := F) G)).map (Int.castRingHom ℂ) =
      Q.map (Polynomial.evalRingHom (Fintype.card F : ℂ))

theorem polyAll_polyPrime {V : Type} [Fintype V] (G : SimpleGraph V) (h : PolyAll G) :
    PolyPrime G := by
  obtain ⟨Q, hQ⟩ := h
  refine ⟨Q, fun p _ => ?_⟩
  have := hQ (ZMod p)
  rwa [ZMod.card] at this

theorem eval_eval_X3 (Q : Polynomial (Polynomial ℂ)) (c : ℂ) :
    (Q.eval (X ^ 3)).eval c = (Q.map (Polynomial.evalRingHom c)).eval (c ^ 3) := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp

/-- Relabelling the vertices does not change the literal count. -/
theorem indepCount_comap {F : Type} [Field F] [Fintype F] {V W : Type} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (e : V ≃ W) (G : SimpleGraph W) (s : ℕ) :
    indepCount (F := F) (cliqueFaces (G.comap e)) s = indepCount (F := F) (cliqueFaces G) s := by
  unfold indepCount
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.arrowCongr e (Equiv.refl _)) ?_)
  intro v
  constructor
  · intro h D hD
    have hC : (G.comap e).IsClique ((D.map e.symm.toEmbedding : Finset V) : Set V) := by
      intro x hx y hy hxy
      rw [Finset.mem_coe, Finset.mem_map_equiv] at hx hy
      simp only [SimpleGraph.comap_adj]
      exact hD (by simpa using hx) (by simpa using hy) (fun h' => hxy (e.injective h'))
    have hl := h _ hC
    let f : D ≃ (D.map e.symm.toEmbedding) :=
      { toFun := fun j => ⟨e.symm j, Finset.mem_map_equiv.2 (by simpa using j.2)⟩
        invFun := fun i => ⟨e i, by simpa using Finset.mem_map_equiv.1 i.2⟩
        left_inv := fun j => by simp
        right_inv := fun i => by simp }
    refine (li_transfer f (fun j : D => (Equiv.arrowCongr e (Equiv.refl _) v) j)
      (fun i : (D.map e.symm.toEmbedding) => v i) (fun _ => 1) (fun j => ?_)).2 hl
    simp [f, Equiv.arrowCongr]
  · intro h C hC
    have hD : G.IsClique ((C.map e.toEmbedding : Finset W) : Set W) := by
      intro x hx y hy hxy
      rw [Finset.mem_coe, Finset.mem_map_equiv] at hx hy
      have := hC (by simpa using hx) (by simpa using hy) (fun h' => hxy (e.symm.injective h'))
      simpa using this
    have hl := h _ hD
    let f : C ≃ (C.map e.toEmbedding) :=
      { toFun := fun j => ⟨e j, Finset.mem_map_equiv.2 (by simpa using j.2)⟩
        invFun := fun i => ⟨e.symm i, Finset.mem_map_equiv.1 i.2⟩
        left_inv := fun j => by simp
        right_inv := fun i => by simp }
    refine (li_transfer f (fun j : C => v j)
      (fun i : (C.map e.toEmbedding) => (Equiv.arrowCongr e (Equiv.refl _) v) i)
      (fun _ => 1) (fun j => ?_)).2 hl
    simp [f, Equiv.arrowCongr]

open Lift in
/-- If every member `H S` (relabelled copies of `G - S`) had polynomial `χ`, the alternating sum
would be one polynomial in `q` equal to `(q-1)^33 |PGL_3| P(q)` at odd primes but `0` at `q = 2`. -/
theorem core {W : Type} [Fintype W] (H : Finset (Sym2 Cop) → SimpleGraph W)
    (hH : ∀ S ∈ Ec.powerset, ∀ (p : ℕ) [Fact p.Prime],
      indepCount (F := ZMod p) (cliqueFaces (H S)) 3 =
        indepCount (F := ZMod p) (cliqueFaces (G.deleteEdges (S : Set (Sym2 Cop)))) 3) :
    ¬ ∀ S ∈ Ec.powerset, PolyPrime (H S) := by
  intro hall
  choose! Qf hQ using hall
  have key : ∀ (p : ℕ) [Fact p.Prime],
      (∑ S ∈ Ec.powerset, ((-1 : ℂ) ^ (#Ec - #S)) * ((Qf S).eval (X ^ 3)).eval (p : ℂ)) =
        (((((Fintype.card (ZMod p) : ℤ) - 1) ^ 26 * (indepCount (F := ZMod p) Δ7 3 : ℤ) : ℤ)) : ℂ) := by
    intro p _
    have hS : ∀ S ∈ Ec.powerset, ((Qf S).eval (X ^ 3)).eval (p : ℂ) =
        (((charPoly (graphArr (F := ZMod p) (G.deleteEdges (S : Set (Sym2 Cop))))).eval
          ((Fintype.card (ZMod p) : ℤ) ^ 3) : ℤ) : ℂ) := by
      intro S hSm
      rw [eval_eval_X3, ← hQ S hSm p]
      have e1 : ((p : ℂ)) ^ 3 = (((Fintype.card (ZMod p) : ℤ) ^ 3 : ℤ) : ℂ) := by
        rw [ZMod.card]; push_cast; ring
      rw [e1, Polynomial.eval_intCast_map, eq_intCast]
      congr 1
      simp only [Int.cast_id]
      rw [← graph_field_count, ← graph_field_count]
      exact congrArg _ (hH S hSm p)
    rw [sum_congr rfl fun S hSm => by rw [hS S hSm]]
    have hL := lift_identity_charPoly (F := ZMod p) 3
    have hI := indepCount_eq (F := ZMod p) Δ7 3
    rw [hI, ← hL]
    push_cast
    rfl
  let R : Polynomial ℂ := ∑ S ∈ Ec.powerset, ((-1 : Polynomial ℂ) ^ (#Ec - #S)) * (Qf S).eval (X ^ 3)
  let E : Polynomial ℂ := (X - 1) ^ 26 * ((X - 1) ^ 7 * X ^ 3 * (X ^ 3 - 1) * (X ^ 2 - 1) *
    (X ^ 6 - 4 * X ^ 5 + 5 * X ^ 4 + 2 * X ^ 3 - 13 * X ^ 2 + 10 * X + 1))
  have hR : ∀ c : ℂ, R.eval c = ∑ S ∈ Ec.powerset, ((-1 : ℂ) ^ (#Ec - #S)) * ((Qf S).eval (X ^ 3)).eval c := by
    intro c
    simp [R, Polynomial.eval_finsetSum]
  have hodd : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → R.eval (p : ℂ) = E.eval (p : ℂ) := by
    intro p _ hp
    rw [hR, key, ZMod.card, Count.indepCount_Δ7_zmod p hp]
    simp only [E, Count.Pq]
    push_cast
    simp
  have hinf : ({p | Nat.Prime p} \ {2} : Set ℕ).Infinite :=
    Nat.infinite_setOfPred_prime.sdiff (Set.finite_singleton 2)
  have himg := hinf.image (f := fun n : ℕ => (n : ℂ)) (fun _ _ _ _ h => Nat.cast_injective h)
  have hsub : ((fun n : ℕ => (n : ℂ)) '' ({p | Nat.Prime p} \ {2})) ⊆ {x | R.eval x = E.eval x} := by
    rintro x ⟨p, ⟨hp, hp2⟩, rfl⟩
    exact @hodd p ⟨hp⟩ (by simpa using hp2)
  have hRE : R = E := Polynomial.eq_of_infinite_eval_eq R E (himg.mono hsub)
  have h2 := key 2
  rw [ZMod.card, Count.indepCount_Δ7_F2, ← hR, hRE] at h2
  simp only [E] at h2
  norm_num at h2

/-- The family on the native vertex type `Cop` itself. -/
theorem not_all_poly_Cop :
    ¬ ∀ S ∈ Lift.Ec.powerset, PolyPrime (Lift.G.deleteEdges (S : Set (Sym2 Lift.Cop))) :=
  core (fun S => Lift.G.deleteEdges (S : Set (Sym2 Lift.Cop))) (fun _ _ _ _ => rfl)

/-- Relabelling `Cop = Fin 11 × Fin 3 ≃ Fin 33`. -/
def e33 : Lift.Cop ≃ Fin 33 := finProdFinEquiv

/-- **Witness on `[ℓ] = Fin 33`**: some `G - S` (relabelled) violates polynomiality even
restricted to prime fields. -/
theorem witness33 : ∃ G : SimpleGraph (Fin 33), ¬ PolyPrime G := by
  by_contra h
  exact core (W := Fin 33)
    (fun S => (Lift.G.deleteEdges (S : Set (Sym2 Lift.Cop))).comap e33.symm)
    (fun S _ p _ => indepCount_comap e33.symm _ 3)
    (fun S _ => Classical.byContradiction fun hn => h ⟨_, hn⟩)

/-- Literal all-prime-power form: some graph on `Fin 33` has no `Q ∈ ℂ[q][t]` valid for all
finite fields. -/
theorem witness33_all : ∃ G : SimpleGraph (Fin 33), ¬ PolyAll G := by
  obtain ⟨G, hG⟩ := witness33
  exact ⟨G, fun h => hG (polyAll_polyPrime G h)⟩

/-- **Native conjunction fails** (MathDB 372486, NTUY Conj.): for any reading `L` of the limit
clause, `∀ ℓ, ∀ G on [ℓ], (P) ∧ L` is false, already through polynomiality (P). -/
theorem ntuy_conjecture_false (L : (ℓ : ℕ) → SimpleGraph (Fin ℓ) → Prop) :
    ¬ ∀ (ℓ : ℕ) (G : SimpleGraph (Fin ℓ)), PolyAll G ∧ L ℓ G := by
  intro h
  obtain ⟨G, hG⟩ := witness33_all
  exact hG (h 33 G).1

theorem ntuy_conjecture_false_prime (L : (ℓ : ℕ) → SimpleGraph (Fin ℓ) → Prop) :
    ¬ ∀ (ℓ : ℕ) (G : SimpleGraph (Fin ℓ)), PolyPrime G ∧ L ℓ G := by
  intro h
  obtain ⟨G, hG⟩ := witness33
  exact hG (h 33 G).1

end Refute
end QArr372486

#print axioms QArr372486.Refute.core
#print axioms QArr372486.Refute.not_all_poly_Cop
#print axioms QArr372486.Refute.witness33
#print axioms QArr372486.Refute.witness33_all
#print axioms QArr372486.Refute.ntuy_conjecture_false
#print axioms QArr372486.Refute.ntuy_conjecture_false_prime
#print axioms QArr372486.Refute.indepCount_comap
```

## QArr372486Audit.lean

```lean
import QArr372486Refute
import QArr372486Mobius

/-! MathDB 372486 independent extracted replay audit (opus-20261117-r1, credit 0).
Expanded readings of NTUY polynomiality (P): the Moebius-lattice `χ` (existential and
universal `μ`), pointwise agreement at every natural `t`, prime fields and all finite fields.
Each reading is proved equivalent to the checked `PolyPrime` / `PolyAll`. No new axioms. -/

noncomputable section
open Polynomial

namespace QArr372486
namespace Audit
open Refute

/-- Agreement at every natural number forces equality of complex polynomials. -/
theorem eq_of_nat_eval (P R : Polynomial ℂ) (h : ∀ n : ℕ, P.eval (n : ℂ) = R.eval (n : ℂ)) :
    P = R := by
  apply Polynomial.eq_of_infinite_eval_eq
  exact (Set.infinite_range_of_injective
    (Nat.cast_injective : Function.Injective (Nat.cast : ℕ → ℂ))).mono
      (by rintro x ⟨n, rfl⟩; exact h n)

theorem polyEq_iff_nat_eval (P R : Polynomial ℂ) :
    P = R ↔ ∀ n : ℕ, P.eval (n : ℂ) = R.eval (n : ℂ) :=
  ⟨fun h n => by rw [h], eq_of_nat_eval P R⟩

theorem polyEq_iff_pointwise (P R : Polynomial ℂ) :
    P = R ↔ ∀ t : ℂ, P.eval t = R.eval t :=
  ⟨fun h t => by rw [h], fun h => eq_of_nat_eval P R (fun n => h n)⟩

/-- (P) pointwise at every natural `t`, prime fields `ZMod p`. -/
def PolyPrimePt {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ Q : Polynomial (Polynomial ℂ), ∀ (p : ℕ) [Fact p.Prime], ∀ n : ℕ,
    (((charPoly (graphArr (F := ZMod p) G)).eval (n : ℤ) : ℤ) : ℂ) =
      (Q.map (Polynomial.evalRingHom (p : ℂ))).eval (n : ℂ)

/-- (P) pointwise at every natural `t`, all finite fields. -/
def PolyAllPt {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ Q : Polynomial (Polynomial ℂ), ∀ (F : Type) [Field F] [Fintype F], ∀ n : ℕ,
    (((charPoly (graphArr (F := F) G)).eval (n : ℤ) : ℤ) : ℂ) =
      (Q.map (Polynomial.evalRingHom (Fintype.card F : ℂ))).eval (n : ℂ)

theorem polyPrimePt_iff {V : Type} [Fintype V] (G : SimpleGraph V) :
    PolyPrimePt G ↔ PolyPrime G := by
  constructor
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, fun p _ => eq_of_nat_eval _ _ fun n => ?_⟩
    rw [Polynomial.eval_natCast_map (Int.castRingHom ℂ), eq_intCast]
    exact hQ p n
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, fun p _ n => ?_⟩
    rw [← hQ p, Polynomial.eval_natCast_map (Int.castRingHom ℂ), eq_intCast]

theorem polyAllPt_iff {V : Type} [Fintype V] (G : SimpleGraph V) :
    PolyAllPt G ↔ PolyAll G := by
  constructor
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, fun F _ _ => eq_of_nat_eval _ _ fun n => ?_⟩
    rw [Polynomial.eval_natCast_map (Int.castRingHom ℂ), eq_intCast]
    exact hQ F n
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, fun F _ _ n => ?_⟩
    rw [← hQ F, Polynomial.eval_natCast_map (Int.castRingHom ℂ), eq_intCast]

/-- Whitney = Moebius on the literal graph arrangement, for any Moebius function `μ`. -/
theorem moebius_eq_charPoly {V : Type} [Fintype V] (G : SimpleGraph V) (F : Type) [Field F]
    [Fintype F] (μ : Submodule F (V → F) → ℤ) (hμ : IsMoebius (graphArr (F := F) G) μ) :
    moebiusCharPoly (graphArr (F := F) G) μ = charPoly (graphArr (F := F) G) :=
  (charPoly_eq_moebiusCharPoly (A := graphArr (F := F) G)
    (top_not_mem_arr (cliqueFaces G)) μ hμ).symm

/-- (P) with NTUY's `χ = ∑_{X ∈ L(A)} μ(X) t^{dim X}`, some Moebius `μ` per field. -/
def PolyAllMob {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ Q : Polynomial (Polynomial ℂ), ∀ (F : Type) [Field F] [Fintype F],
    ∃ μ : Submodule F (V → F) → ℤ, IsMoebius (graphArr (F := F) G) μ ∧
      (moebiusCharPoly (graphArr (F := F) G) μ).map (Int.castRingHom ℂ) =
        Q.map (Polynomial.evalRingHom (Fintype.card F : ℂ))

/-- (P) with NTUY's `χ`, every Moebius `μ`. -/
def PolyAllMobUniv {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ Q : Polynomial (Polynomial ℂ), ∀ (F : Type) [Field F] [Fintype F],
    ∀ μ : Submodule F (V → F) → ℤ, IsMoebius (graphArr (F := F) G) μ →
      (moebiusCharPoly (graphArr (F := F) G) μ).map (Int.castRingHom ℂ) =
        Q.map (Polynomial.evalRingHom (Fintype.card F : ℂ))

theorem polyAllMob_iff {V : Type} [Fintype V] (G : SimpleGraph V) :
    PolyAllMob G ↔ PolyAll G := by
  constructor
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, fun F _ _ => ?_⟩
    obtain ⟨μ, hμ, h⟩ := hQ F
    rwa [moebius_eq_charPoly G F μ hμ] at h
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, fun F _ _ => ⟨whitneyCoeff (graphArr (F := F) G),
      arr_isMoebius_whitney (F := F) (cliqueFaces G), ?_⟩⟩
    rw [moebius_eq_charPoly G F (whitneyCoeff (graphArr (F := F) G))
      (arr_isMoebius_whitney (F := F) (cliqueFaces G))]
    exact hQ F

theorem polyAllMobUniv_iff {V : Type} [Fintype V] (G : SimpleGraph V) :
    PolyAllMobUniv G ↔ PolyAll G := by
  constructor
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, fun F _ _ => ?_⟩
    have h := hQ F _ (arr_isMoebius_whitney (F := F) (cliqueFaces G))
    rwa [moebius_eq_charPoly G F _ (arr_isMoebius_whitney (F := F) (cliqueFaces G))] at h
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, fun F _ _ μ hμ => ?_⟩
    rw [moebius_eq_charPoly G F μ hμ]
    exact hQ F

/-- One explicit-family graph on `Fin 33` violates every recorded reading of (P). -/
theorem witness33_readings : ∃ G : SimpleGraph (Fin 33),
    ¬ PolyPrime G ∧ ¬ PolyAll G ∧ ¬ PolyPrimePt G ∧ ¬ PolyAllPt G ∧
      ¬ PolyAllMob G ∧ ¬ PolyAllMobUniv G := by
  obtain ⟨G, hG⟩ := witness33
  have hA : ¬ PolyAll G := fun h => hG (polyAll_polyPrime G h)
  exact ⟨G, hG, hA, fun h => hG ((polyPrimePt_iff G).1 h), fun h => hA ((polyAllPt_iff G).1 h),
    fun h => hA ((polyAllMob_iff G).1 h), fun h => hA ((polyAllMobUniv_iff G).1 h)⟩

/-- The native conjunction `∀ ℓ G, (P) ∧ L` fails for every `L` under each reading. -/
theorem ntuy_false_readings (L : (ℓ : ℕ) → SimpleGraph (Fin ℓ) → Prop) :
    (¬ ∀ (ℓ : ℕ) (G : SimpleGraph (Fin ℓ)), PolyAll G ∧ L ℓ G) ∧
    (¬ ∀ (ℓ : ℕ) (G : SimpleGraph (Fin ℓ)), PolyPrime G ∧ L ℓ G) ∧
    (¬ ∀ (ℓ : ℕ) (G : SimpleGraph (Fin ℓ)), PolyPrimePt G ∧ L ℓ G) ∧
    (¬ ∀ (ℓ : ℕ) (G : SimpleGraph (Fin ℓ)), PolyAllPt G ∧ L ℓ G) ∧
    (¬ ∀ (ℓ : ℕ) (G : SimpleGraph (Fin ℓ)), PolyAllMob G ∧ L ℓ G) ∧
    (¬ ∀ (ℓ : ℕ) (G : SimpleGraph (Fin ℓ)), PolyAllMobUniv G ∧ L ℓ G) := by
  obtain ⟨G, h1, h2, h3, h4, h5, h6⟩ := witness33_readings
  exact ⟨fun h => h2 (h 33 G).1, fun h => h1 (h 33 G).1, fun h => h3 (h 33 G).1,
    fun h => h4 (h 33 G).1, fun h => h5 (h 33 G).1, fun h => h6 (h 33 G).1⟩

end Audit
end QArr372486

-- Read-only transitive axiom sweep over every constant of the nine modules and this audit.
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let names := env.constants.fold (fun (acc : Array Name) n _ =>
    let s := n.toString
    if s.startsWith "QArr372486" || s.startsWith "_private.QArr372486" then acc.push n
    else acc) #[]
  let mut used : Array Name := #[]
  let mut bad : Array Name := #[]
  for n in names do
    let axs ← collectAxioms n
    for a in axs do
      if !used.contains a then used := used.push a
    if axs.any (fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound) then
      bad := bad.push n
  logInfo m!"AUDIT_SWEEP constants={names.size} axioms_used={used} nonstandard={bad.size} {bad}"

#print axioms QArr372486.Audit.witness33_readings
#print axioms QArr372486.Audit.ntuy_false_readings
#print axioms QArr372486.Audit.polyEq_iff_pointwise
#print axioms QArr372486.Audit.polyAllMob_iff
#print axioms QArr372486.Audit.polyAllMobUniv_iff
#print axioms QArr372486.Audit.polyPrimePt_iff
#print axioms QArr372486.Audit.polyAllPt_iff
#print axioms QArr372486.Refute.ntuy_conjecture_false
#print axioms QArr372486.Refute.ntuy_conjecture_false_prime
#print axioms QArr372486.Refute.witness33_all
#print axioms QArr372486.Count.indepCount_Δ7_odd
#print axioms QArr372486.Count.indepCount_Δ7_even
#print axioms QArr372486.Count.indepCount_Δ7_F2
#print axioms QArr372486.Lift.lift_identity_charPoly
#print axioms QArr372486.arr_eq_ntuy
#print axioms QArr372486.graph_field_count_moebius
```

