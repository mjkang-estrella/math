# Lean source appendix for MathDB 340107

Modules are listed in import order.

### `PrimitiveAvoidance.lean`

```lean
import Mathlib.Combinatorics.SetFamily.FourFunctions
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Preorder.Finite
import Mathlib.Order.UpperLower.Closure

open Set Finset

namespace PrimitiveRatio

section Posets

variable {α : Type*} [PartialOrder α]

/-- Antichains supported in a specified subset of a poset. -/
def AntichainsIn (s : Set α) := {t : Set α // t ⊆ s ∧ IsAntichain (· ≤ ·) t}

instance [Finite α] (s : Set α) : Finite (AntichainsIn s) := by
  unfold AntichainsIn
  infer_instance

instance [Finite α] : Finite (LowerSet α) :=
  Finite.of_injective (fun I : LowerSet α => (I : Set α)) SetLike.coe_injective

/-- Transfer antichains on an induced subposet along its subtype inclusion. -/
noncomputable def antichainsSubtype (r : Set α) (s : Set r) :
    AntichainsIn s ≃ AntichainsIn (Subtype.val '' s) where
  toFun t := ⟨Subtype.val '' t.1, image_mono t.2.1, by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy hle
    exact t.2.2 hx hy (fun h => hxy (congrArg Subtype.val h)) hle⟩
  invFun t := ⟨Subtype.val ⁻¹' t.1, by
    intro x hx
    obtain ⟨y, hy, he⟩ := t.2.1 hx
    exact (Subtype.ext he : y = x) ▸ hy, by
    intro x hx y hy hxy hle
    exact t.2.2 hx hy (fun h => hxy (Subtype.ext h)) hle⟩
  left_inv t := Subtype.ext (preimage_image_eq _ Subtype.val_injective)
  right_inv t := Subtype.ext (image_preimage_eq_of_subset (t.2.1.trans (image_subset_range _ _)))

/-- Downward closure and maximal elements give mutually inverse maps. -/
noncomputable def antichainsLower [Finite α] (C : LowerSet α) :
    AntichainsIn (C : Set α) ≃ {I : LowerSet α // I ≤ C} where
  toFun t := ⟨lowerClosure t.1, lowerClosure_le.mpr t.2.1⟩
  invFun I := ⟨{x | Maximal (· ∈ I.1) x}, fun _ hx => I.2 hx.prop,
    setOfPred_maximal_antichain _⟩
  left_inv t := Subtype.ext (Set.ext fun _ => t.2.2.maximal_mem_lowerClosure_iff_mem)
  right_inv I := by
    apply Subtype.ext
    apply SetLike.ext
    intro x
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact I.1.lower hxy hy.prop
    · intro hx
      obtain ⟨y, hxy, hy⟩ := (Set.toFinite (I.1 : Set α)).exists_le_maximal hx
      exact ⟨y, hy, hxy⟩

variable (A : LowerSet α)

private abbrev Outside := {x : α // x ∉ A}
private abbrev Inside := {x : α // x ∈ A}

private def restrictOutside (C : LowerSet α) : LowerSet (Outside A) :=
  ⟨Subtype.val ⁻¹' (C : Set α), fun {_ _} h hx => C.lower h hx⟩

private def Extensions (J : LowerSet (Outside A)) :=
  {K : LowerSet (Inside A) // ∀ (x : Inside A) (y : Outside A), x.1 ≤ y.1 → y ∈ J → x ∈ K}

private instance [Finite α] (J : LowerSet (Outside A)) :
    Finite (Extensions A J) := by unfold Extensions; infer_instance

private def joinParts (J : LowerSet (Outside A)) (K : Extensions A J) : LowerSet α where
  carrier := (Subtype.val '' (J : Set (Outside A))) ∪ (Subtype.val '' (K.1 : Set (Inside A)))
  lower' := by
    intro y x hxy hy
    rcases hy with ⟨j, hj, rfl⟩ | ⟨k, hk, rfl⟩
    · by_cases hx : x ∈ A
      · exact Or.inr ⟨⟨x, hx⟩, K.2 _ _ hxy hj, rfl⟩
      · exact Or.inl ⟨⟨x, hx⟩, J.lower hxy hj, rfl⟩
    · exact Or.inr ⟨⟨x, A.lower hxy k.2⟩, K.1.lower hxy hk, rfl⟩

private lemma mem_join_outside (J : LowerSet (Outside A)) (K : Extensions A J)
    (x : Outside A) : x.1 ∈ joinParts A J K ↔ x ∈ J := by
  constructor
  · rintro (⟨y, hy, he⟩ | ⟨y, _, he⟩)
    · exact (Subtype.ext he : y = x) ▸ hy
    · exact (x.2 (he ▸ y.2)).elim
  · exact fun hx => Or.inl ⟨x, hx, rfl⟩

private lemma mem_join_inside (J : LowerSet (Outside A)) (K : Extensions A J)
    (x : Inside A) : x.1 ∈ joinParts A J K ↔ x ∈ K.1 := by
  constructor
  · rintro (⟨y, _, he⟩ | ⟨y, hy, he⟩)
    · exact (y.2 (he.symm ▸ x.2)).elim
    · exact (Subtype.ext he : y = x) ▸ hy
  · exact fun hx => Or.inr ⟨x, hx, rfl⟩

/-- A lower set supported in C splits into its outside part and an extension inside A. -/
private noncomputable def splitParts (C : LowerSet α) (hAC : A ≤ C) :
    {I : LowerSet α // I ≤ C} ≃
      Σ J : {J : LowerSet (Outside A) // J ≤ restrictOutside A C}, Extensions A J.1 where
  toFun I := ⟨⟨restrictOutside A I.1, fun _ hx => I.2 hx⟩,
    ⟨⟨Subtype.val ⁻¹' (I.1 : Set α), fun {_ _} h hx => I.1.lower h hx⟩,
      fun _ _ h hy => I.1.lower h hy⟩⟩
  invFun D := ⟨joinParts A D.1.1 D.2, by
    rintro _ (⟨x, hx, rfl⟩ | ⟨x, _, rfl⟩)
    · exact D.1.2 hx
    · exact hAC x.2⟩
  left_inv I := by
    apply Subtype.ext
    apply SetLike.ext
    intro x
    by_cases hx : x ∈ A
    · exact mem_join_inside A _ _ ⟨x, hx⟩
    · exact mem_join_outside A _ _ ⟨x, hx⟩
  right_inv := by
    rintro ⟨⟨J, hJ⟩, K⟩
    have h : restrictOutside A (joinParts A J K) = J :=
      SetLike.ext fun x => mem_join_outside A J K x
    have h' : (⟨restrictOutside A (joinParts A J K), fun x hx =>
        (mem_join_outside A J K x).mp hx |> hJ⟩ :
        {J : LowerSet (Outside A) // J ≤ restrictOutside A C}) = ⟨J, hJ⟩ := Subtype.ext h
    refine Sigma.ext h' ?_
    apply (Subtype.heq_iff_coe_eq (h := ?_)).mpr
    · exact SetLike.ext fun x => mem_join_inside A J K x
    · intro L
      change (∀ (x : Inside A) (y : Outside A), x.1 ≤ y.1 →
        y ∈ restrictOutside A (joinParts A J K) → x ∈ L) ↔ _
      rw [h]

private lemma card_avoiding [Finite α] (C : LowerSet α) :
    Nat.card (AntichainsIn ((C : Set α) \ (A : Set α))) =
    Nat.card {J : LowerSet (Outside A) // J ≤ restrictOutside A C} := by
  rw [← Nat.card_congr (antichainsLower (restrictOutside A C))]
  have h : Subtype.val '' (restrictOutside A C : Set (Outside A)) = (C : Set α) \ (A : Set α) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.2⟩
    · exact fun hx => ⟨⟨x, hx.2⟩, hx.1, rfl⟩
  rw [← h]
  exact (Nat.card_congr (antichainsSubtype (SetLike.coe A)ᶜ _)).symm

private lemma weight_antitone [Finite α] :
    Antitone (fun J : LowerSet (Outside A) => Nat.card (Extensions A J)) := by
  intro J L h
  exact Nat.card_le_card_of_injective
    (fun t : Extensions A L => (⟨t.1, fun x y hxy hy => t.2 x y hxy (h hy)⟩ : Extensions A J))
    (fun _ _ he => Subtype.ext (congrArg (fun t : Extensions A J => t.1) he))

private lemma card_parts {L : Type*} [Fintype L]
    (E : L → Type*) [∀ x, Finite (E x)] (F : L → Prop) [DecidablePred F] :
    Nat.card (Σ x : Subtype F, E x.1) = ∑ x : L, if F x then Nat.card (E x) else 0 := by
  classical
  let : Fintype (Subtype F) := Fintype.ofFinite _
  let (x : Subtype F) : Fintype (E x.1) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp_rw [Fintype.card_eq_nat_card]
  rw [← Finset.sum_subtype (Finset.univ.filter F) (fun x => by simp)
    (fun x => Nat.card (E x)), Finset.sum_filter]

private lemma card_total [Finite α] [Fintype (LowerSet (Outside A))]
    [DecidableRel (fun a b : LowerSet (Outside A) => a ≤ b)]
    (C : LowerSet α) (hAC : A ≤ C) :
    Nat.card (AntichainsIn (C : Set α)) =
    ∑ J : LowerSet (Outside A), if J ≤ restrictOutside A C then Nat.card (Extensions A J) else 0 := by
  classical
  rw [Nat.card_congr (antichainsLower C), Nat.card_congr (splitParts A C hAC)]
  exact card_parts (Extensions A) _

private lemma card_indicator {L : Type*} [Fintype L] (F : L → Prop) [DecidablePred F] :
    Nat.card (Subtype F) = ∑ x : L, if F x then 1 else 0 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact (by simp : (Finset.univ.filter F).card = ∑ _ ∈ Finset.univ.filter F, (1 : ℕ)).trans
    (Finset.sum_filter (p := F) (f := fun _ : L => (1 : ℕ)))

/-- The avoidance fraction increases when the supporting lower set grows.
The statement is cross-multiplied so no division is needed. -/
theorem avoidance_mono [Finite α] (C P : LowerSet α) (hAC : A ≤ C) (hCP : C ≤ P) :
    Nat.card (AntichainsIn ((C : Set α) \ (A : Set α))) * Nat.card (AntichainsIn (P : Set α)) ≤
    Nat.card (AntichainsIn ((P : Set α) \ (A : Set α))) * Nat.card (AntichainsIn (C : Set α)) := by
  classical
  let : Fintype (LowerSet (Outside A)) := Fintype.ofFinite _
  let w (J : (LowerSet (Outside A))ᵒᵈ) := Nat.card (Extensions A J)
  let ind (D : LowerSet α) (J : (LowerSet (Outside A))ᵒᵈ) : ℕ :=
    if J.ofDual ≤ restrictOutside A D then 1 else 0
  have hmono (D : LowerSet α) : Monotone (ind D) := by
    intro a b hab
    change b.ofDual ≤ a.ofDual at hab
    by_cases h : a.ofDual ≤ restrictOutside A D
    · simp [ind, h, hab.trans h]
    · simp [ind, h]
  have hw : Monotone w := fun _ _ h => weight_antitone A h
  have hμ (a b : (LowerSet (Outside A))ᵒᵈ) :
      ind P a * ind P b ≤ ind P (a ⊓ b) * ind P (a ⊔ b) := by
    by_cases ha : a.ofDual ≤ restrictOutside A P
    · by_cases hb : b.ofDual ≤ restrictOutside A P
      · have hs : a.ofDual ⊔ b.ofDual ≤ restrictOutside A P := sup_le ha hb
        have hi : a.ofDual ⊓ b.ofDual ≤ restrictOutside A P := inf_le_left.trans ha
        change (if a.ofDual ≤ _ then 1 else 0) * (if b.ofDual ≤ _ then 1 else 0) ≤
          (if a.ofDual ⊔ b.ofDual ≤ _ then 1 else 0) *
          (if a.ofDual ⊓ b.ofDual ≤ _ then 1 else 0)
        simp [ha, hb, hs, hi]
      · simp [ind, hb]
    · simp [ind, ha]
  have hmul (J : (LowerSet (Outside A))ᵒᵈ) :
      ind P J * ind C J = ind C J := by
    by_cases h : J.ofDual ≤ restrictOutside A C
    · have hh : J.ofDual ≤ restrictOutside A P := fun _ hx => hCP (h hx)
      simp [ind, h, hh]
    · simp [ind, h]
  have h (D : LowerSet α) (hAD : A ≤ D) :
      (∑ J : (LowerSet (Outside A))ᵒᵈ, ind D J * w J) =
        Nat.card (AntichainsIn (D : Set α)) := by
    rw [card_total A D hAD]
    apply Finset.sum_congr rfl
    intro J _
    change ind D J * w J = (if J.ofDual ≤ restrictOutside A D then Nat.card (Extensions A J) else 0)
    by_cases hJ : J.ofDual ≤ restrictOutside A D <;> simp [ind, w, hJ]
  have h' (D : LowerSet α) :
      (∑ J : (LowerSet (Outside A))ᵒᵈ, ind D J) =
        Nat.card (AntichainsIn ((D : Set α) \ (A : Set α))) := by
    rw [card_avoiding A D, card_indicator]
    rfl
  have hfkg := fkg (μ := ind P) (f := ind C) (g := w)
    (fun _ => Nat.zero_le _) (fun _ => Nat.zero_le _) (fun _ => Nat.zero_le _)
    (hmono C) hw hμ
  simp_rw [hmul, ← mul_assoc, hmul] at hfkg
  rwa [h' C, h' P, h C hAC, h P (hAC.trans hCP)] at hfkg

end Posets

end PrimitiveRatio
```

### `PrimitiveCounts.lean`

```lean
import PrimitiveAvoidance
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Finset
open scoped Classical

namespace PrimitiveRatio

def IsPrimitive (S : Finset ℕ) : Prop := ∀ a ∈ S, ∀ b ∈ S, a ∣ b → a = b

noncomputable def Q (k : ℕ) : ℕ := ((Finset.Icc 1 k).powerset.filter IsPrimitive).card

noncomputable def g (k : ℕ) : ℚ :=
  if k ≤ 1 then 1 else (Q k : ℚ) / (Q (k - 1) : ℚ) - 1

noncomputable def family (s : Finset ℕ) := s.powerset.filter IsPrimitive

noncomputable def count (s : Finset ℕ) := (family s).card

@[simp] lemma mem_family {s t : Finset ℕ} : t ∈ family s ↔ t ⊆ s ∧ IsPrimitive t := by
  simp [family]

lemma IsPrimitive.mono {s t : Finset ℕ} (h : IsPrimitive t) (hst : s ⊆ t) : IsPrimitive s :=
  fun a ha b hb => h a (hst ha) b (hst hb)

lemma count_pos (s : Finset ℕ) : 0 < count s :=
  Finset.card_pos.mpr ⟨∅, mem_family.mpr ⟨empty_subset _, by simp [IsPrimitive]⟩⟩

@[simp] lemma count_empty : count ∅ = 1 := by
  change (family ∅).card = 1
  have h : family ∅ = {∅} := by
    ext t
    simp [subset_empty]
    intro h
    subst t
    simp [IsPrimitive]
  rw [h, card_singleton]

lemma count_mono {s t : Finset ℕ} (h : s ⊆ t) : count s ≤ count t :=
  Finset.card_le_card fun _ hx => mem_family.mpr ⟨(mem_family.mp hx).1.trans h, (mem_family.mp hx).2⟩

lemma Q_zero : Q 0 = 1 := by
  change count (Icc 1 0) = 1
  rw [show (Icc 1 0 : Finset ℕ) = ∅ from Icc_eq_empty_of_lt (by decide), count_empty]

lemma g_one : g 1 = 1 := by simp [g]

/-- The divisor poset carried by a finite set of natural numbers. -/
def DivisorPoset (u : Finset ℕ) := {x : ℕ // x ∈ u}

instance (u : Finset ℕ) : Finite (DivisorPoset u) := inferInstanceAs (Finite ↥u)

def divisorValue {u : Finset ℕ} (x : DivisorPoset u) : ℕ := Subtype.val x

lemma divisorValue_mem {u : Finset ℕ} (x : DivisorPoset u) : divisorValue x ∈ u :=
  Subtype.property x

lemma divisorValue_injective (u : Finset ℕ) : Function.Injective (@divisorValue u) :=
  Subtype.val_injective

instance (u : Finset ℕ) : PartialOrder (DivisorPoset u) where
  le a b := divisorValue a ∣ divisorValue b
  le_refl _ := dvd_refl _
  le_trans _ _ _ := dvd_trans
  le_antisymm _ _ hab hba := divisorValue_injective u (Nat.dvd_antisymm hab hba)

private noncomputable def countEquiv {s u : Finset ℕ} (hs : s ⊆ u) :
    ↥(family s) ≃ AntichainsIn {x : DivisorPoset u | divisorValue x ∈ s} where
  toFun t := ⟨{x | divisorValue x ∈ t.1}, (fun _ hx => (mem_family.mp t.2).1 hx), by
    intro a ha b hb hne hle
    exact hne (divisorValue_injective u ((mem_family.mp t.2).2 _ ha _ hb hle))⟩
  invFun t := ⟨(Set.toFinite t.1).toFinset.image divisorValue, mem_family.mpr ⟨by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    exact t.2.1 ((Set.Finite.mem_toFinset _).mp hy), by
    intro a ha b hb hab
    obtain ⟨x, hx, rfl⟩ := mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hb
    exact congrArg divisorValue (t.2.2.eq ((Set.Finite.mem_toFinset _).mp hx) ((Set.Finite.mem_toFinset _).mp hy) hab)⟩⟩
  left_inv t := by
    apply Subtype.ext
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      exact (show y ∈ {x : DivisorPoset u | divisorValue x ∈ t.1} from (Set.Finite.mem_toFinset _).mp hy)
    · intro hx
      let y : DivisorPoset u := ⟨x, hs ((mem_family.mp t.2).1 hx)⟩
      exact mem_image.mpr ⟨y, (Set.Finite.mem_toFinset _).mpr (show divisorValue y ∈ t.1 from hx), rfl⟩
  right_inv t := by
    apply Subtype.ext
    ext x
    change divisorValue x ∈ (Set.toFinite t.1).toFinset.image divisorValue ↔ x ∈ t.1
    constructor
    · intro hx
      obtain ⟨y, hy, he⟩ := mem_image.mp hx
      exact (divisorValue_injective u he) ▸ (Set.Finite.mem_toFinset _).mp hy
    · exact fun hx => mem_image.mpr ⟨x, (Set.Finite.mem_toFinset _).mpr hx, rfl⟩

lemma count_eq_chains {s u : Finset ℕ} (hs : s ⊆ u) :
    count s = Nat.card (AntichainsIn {x : DivisorPoset u | divisorValue x ∈ s}) := by
  rw [← Nat.card_congr (countEquiv hs), Nat.card_eq_fintype_card, Fintype.card_coe]
  rfl

/-- The lower-set inequality in the divisor order on the ambient set u. -/
lemma count_avoidance {s t u : Finset ℕ} (hst : s ⊆ t) (htu : t ⊆ u)
    (hs : ∀ x ∈ u, ∀ y ∈ s, x ∣ y → x ∈ s)
    (ht : ∀ x ∈ u, ∀ y ∈ t, x ∣ y → x ∈ t) :
    count (t \ s) * count u ≤ count (u \ s) * count t := by
  let A : LowerSet (DivisorPoset u) :=
    ⟨{x | divisorValue x ∈ s}, fun {y x} h hy => hs _ (divisorValue_mem x) _ hy h⟩
  let C : LowerSet (DivisorPoset u) :=
    ⟨{x | divisorValue x ∈ t}, fun {y x} h hy => ht _ (divisorValue_mem x) _ hy h⟩
  rw [count_eq_chains ((sdiff_subset : t \ s ⊆ t).trans htu), count_eq_chains (Subset.rfl : u ⊆ u),
    count_eq_chains (sdiff_subset : u \ s ⊆ u), count_eq_chains htu]
  have hu : {x : DivisorPoset u | divisorValue x ∈ u} = (⊤ : LowerSet (DivisorPoset u)).carrier := by
    ext x
    exact iff_of_true (divisorValue_mem x) trivial
  simp only [mem_sdiff, Set.ofPred_and]
  rw [hu]
  exact avoidance_mono A C ⊤ (fun _ hx => hst hx) le_top

def below (k : ℕ) : Finset ℕ := Ico 1 k

def target (k : ℕ) : Finset ℕ := (below k).filter (· ∣ k)

@[simp] lemma mem_below {k x : ℕ} : x ∈ below k ↔ 0 < x ∧ x < k := by
  simp [below, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]

@[simp] lemma mem_target {k x : ℕ} : x ∈ target k ↔ x ∈ below k ∧ x ∣ k := mem_filter

lemma below_eq_Icc (k : ℕ) : below k = Icc 1 (k - 1) := by
  ext x
  simp only [mem_below, mem_Icc]
  omega

private lemma insert_top (k : ℕ) (s : Finset ℕ) (hs : s ⊆ below k) :
    IsPrimitive (insert k s) ↔ IsPrimitive s ∧ s ⊆ below k \ target k := by
  constructor
  · intro hi
    refine ⟨hi.mono (subset_insert _ _), fun x hx => mem_sdiff.mpr ⟨hs hx, ?_⟩⟩
    intro hd
    have he := hi x (mem_insert_of_mem hx) k (mem_insert_self _ _) (mem_target.mp hd).2
    exact (mem_below.mp (hs hx)).2.ne he
  · rintro ⟨hp, hd⟩ a ha b hb hab
    rcases mem_insert.mp ha with rfl | ha
    · rcases mem_insert.mp hb with rfl | hb
      · rfl
      · exact False.elim ((mem_below.mp (hs hb)).2.not_ge (Nat.le_of_dvd (mem_below.mp (hs hb)).1 hab))
    · rcases mem_insert.mp hb with he | hb
      · subst b
        exact False.elim ((mem_sdiff.mp (hd ha)).2 (mem_target.mpr ⟨hs ha, hab⟩))
      · exact hp a ha b hb hab

lemma Q_split (k : ℕ) (hk : 0 < k) : Q k = count (below k) + count (below k \ target k) := by
  classical
  let old := family (below k)
  let new := (family (below k \ target k)).image (insert k)
  have hn {s : Finset ℕ} (hs : s ∈ family (below k \ target k)) : k ∉ s := fun h =>
    (mem_below.mp (mem_sdiff.mp ((mem_family.mp hs).1 h)).1).2.false
  have hcard : new.card = count (below k \ target k) := by
    apply card_image_of_injOn
    intro s hs t ht he
    have h := congrArg (fun z : Finset ℕ => z.erase k) he
    simpa only [erase_insert (hn hs), erase_insert (hn ht)] using h
  have hdis : Disjoint old new := by
    refine disjoint_left.mpr ?_
    intro s hs ht
    obtain ⟨t, _, rfl⟩ := mem_image.mp ht
    exact (mem_below.mp ((mem_family.mp hs).1 (mem_insert_self _ _))).2.false
  change (family (Icc 1 k)).card = old.card + count (below k \ target k)
  rw [← hcard, ← card_union_of_disjoint hdis]
  congr 1
  ext s
  simp only [mem_family, mem_union, new, old, mem_image]
  constructor
  · rintro ⟨hs, hp⟩
    by_cases hm : k ∈ s
    · right
      have hsub : s.erase k ⊆ below k := by
        intro x hx
        have h := mem_Icc.mp (hs (mem_erase.mp hx).2)
        exact mem_below.mpr ⟨by omega, by have := (mem_erase.mp hx).1; omega⟩
      have he := insert_erase hm
      have hi : IsPrimitive (insert k (s.erase k)) := he.symm ▸ hp
      obtain ⟨hprim, hav⟩ := (insert_top k (s.erase k) hsub).mp hi
      exact ⟨s.erase k, ⟨hav, hprim⟩, he⟩
    · left
      refine ⟨fun x hx => ?_, hp⟩
      have h := mem_Icc.mp (hs hx)
      exact mem_below.mpr ⟨by omega, by exact lt_of_le_of_ne h.2 (by rintro rfl; exact hm hx)⟩
  · rintro (⟨hs, hp⟩ | ⟨t, ⟨ht, hp⟩, rfl⟩)
    · exact ⟨fun x hx => by have h := mem_below.mp (hs hx); exact mem_Icc.mpr ⟨h.1, h.2.le⟩, hp⟩
    · have hsub : t ⊆ below k := ht.trans sdiff_subset
      refine ⟨?_, (insert_top k t hsub).mpr ⟨hp, ht⟩⟩
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact mem_Icc.mpr ⟨hk, le_rfl⟩
      · have h := mem_below.mp (hsub hx)
        exact mem_Icc.mpr ⟨h.1, h.2.le⟩

lemma g_ratio (k : ℕ) (hk : 0 < k) :
    g k = (count (below k \ target k) : ℚ) / count (below k) := by
  by_cases h : k ≤ 1
  · have he : k = 1 := by omega
    subst k
    have hz : below 1 = ∅ := by ext x; simp; omega
    simp [g_one, hz]
  · have hq : Q (k - 1) = count (below k) := by rw [below_eq_Icc]; rfl
    have hn : (count (below k) : ℚ) ≠ 0 := ne_of_gt (by exact_mod_cast count_pos (below k))
    rw [g, ite_eq_right h, Q_split k hk, hq, Nat.cast_add, add_div, div_self hn]
    ring

lemma g_nonneg (k : ℕ) (hk : 0 < k) : 0 ≤ g k := by rw [g_ratio k hk]; positivity

lemma g_le_one (k : ℕ) (hk : 0 < k) : g k ≤ 1 := by
  have hp : (0 : ℚ) < count (below k) := by exact_mod_cast count_pos (below k)
  rw [g_ratio k hk, div_le_iff₀ hp, one_mul]
  exact_mod_cast count_mono (sdiff_subset : below k \ target k ⊆ below k)

end PrimitiveRatio
```

### `PrimitiveBlocks.lean`

```lean
import PrimitiveCounts
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Preimage

open Finset
open scoped Classical

namespace PrimitiveRatio

private def Compatible (t : Finset ℕ) (x : ℕ) :=
  ∀ y ∈ t, ¬ y ∣ x ∧ ¬ x ∣ y

private noncomputable def allowed (s B t : Finset ℕ) :=
  (s ∩ B).filter (Compatible t)

@[simp] private lemma mem_allowed {s B t : Finset ℕ} {x : ℕ} :
    x ∈ allowed s B t ↔ (x ∈ s ∧ x ∈ B) ∧ Compatible t x := by
  simp [allowed]

private lemma union_primitive {t u : Finset ℕ} (ht : IsPrimitive t) (hu : IsPrimitive u)
    (h : ∀ x ∈ u, Compatible t x) : IsPrimitive (t ∪ u) := by
  intro a ha b hb hab
  rcases mem_union.mp ha with ha | ha <;> rcases mem_union.mp hb with hb | hb
  · exact ht a ha b hb hab
  · exact ((h b hb a ha).1 hab).elim
  · exact ((h a ha b hb).2 hab).elim
  · exact hu a ha b hb hab

/-- Within a fiber, intersection with the block is inverse to adjoining the outside antichain. -/
private lemma fiber_card (s B t : Finset ℕ) (ht : t ∈ family (s \ B)) :
    ((family s).filter (fun v => v \ B = t)).card = count (allowed s B t) := by
  obtain ⟨hts, htp⟩ := mem_family.mp ht
  change _ = (family (allowed s B t)).card
  refine card_bij' (fun v _ => v ∩ B) (fun u _ => t ∪ u) ?_ ?_ ?_ ?_
  · intro v hv
    obtain ⟨hvs, hvp⟩ := mem_family.mp (mem_filter.mp hv).1
    have he := (mem_filter.mp hv).2
    refine mem_family.mpr ⟨?_, hvp.mono inter_subset_left⟩
    intro x hx
    obtain ⟨hxv, hxB⟩ := mem_inter.mp hx
    refine mem_allowed.mpr ⟨⟨hvs hxv, hxB⟩, fun y hy => ?_⟩
    have hy' := mem_sdiff.mp (he ▸ hy : y ∈ v \ B)
    have hne : y ≠ x := fun eq => hy'.2 (eq ▸ hxB)
    exact ⟨fun h => hne (hvp y hy'.1 x hxv h), fun h => hne (hvp x hxv y hy'.1 h).symm⟩
  · intro u hu
    obtain ⟨hus, hup⟩ := mem_family.mp hu
    refine mem_filter.mpr ⟨mem_family.mpr ⟨?_, union_primitive htp hup ?_⟩, ?_⟩
    · exact union_subset (hts.trans sdiff_subset) (fun x hx => (mem_allowed.mp (hus hx)).1.1)
    · exact fun x hx => (mem_allowed.mp (hus hx)).2
    · ext x
      have htB : x ∈ t → x ∉ B := fun hx => (mem_sdiff.mp (hts hx)).2
      have huB : x ∈ u → x ∈ B := fun hx => (mem_allowed.mp (hus hx)).1.2
      simp only [mem_sdiff, mem_union]
      tauto
  · intro v hv
    rw [← (mem_filter.mp hv).2, sdiff_union_inter]
  · intro u hu
    ext x
    have htB : x ∈ t → x ∉ B := fun hx => (mem_sdiff.mp (hts hx)).2
    have huB : x ∈ u → x ∈ B := fun hx => (mem_allowed.mp ((mem_family.mp hu).1 hx)).1.2
    simp only [mem_inter, mem_union]
    tauto

private lemma sum_fibers (s B : Finset ℕ) :
    count s = ∑ t ∈ family (s \ B), count (allowed s B t) := by
  change (family s).card = _
  rw [card_eq_sum_card_fiberwise (f := fun v : Finset ℕ => v \ B)
    (t := family (s \ B)) (fun v hv => ?_)]
  · exact sum_congr rfl (fun t ht => fiber_card s B t ht)
  · obtain ⟨hvs, hvp⟩ := mem_family.mp hv
    exact mem_family.mpr ⟨fun _ hx => mem_sdiff.mpr ⟨hvs (mem_sdiff.mp hx).1, (mem_sdiff.mp hx).2⟩,
      hvp.mono sdiff_subset⟩

private lemma allowed_sdiff (s B V t : Finset ℕ) :
    allowed (s \ V) B t = allowed s B t \ V := by
  ext x
  simp only [mem_allowed, mem_sdiff]
  tauto

private lemma allowed_sdiff_outside (s B V t : Finset ℕ) :
    allowed (s \ (V \ B)) B t = allowed s B t := by
  ext x
  simp only [mem_allowed, mem_sdiff]
  tauto

/-- Sum the bound over the same outside antichains in the numerator and denominator. -/
private lemma conditional_count (s B V : Finset ℕ) (den num : ℕ)
    (h : ∀ t ∈ family ((s \ B) \ V),
      count (allowed s B t \ V) * den ≤ num * count (allowed s B t)) :
    count (s \ V) * den ≤ num * count (s \ (V \ B)) := by
  have h₁ : (s \ V) \ B = (s \ B) \ V := by
    ext x
    simp only [mem_sdiff]
    tauto
  have h₂ : (s \ (V \ B)) \ B = (s \ B) \ V := by
    ext x
    simp only [mem_sdiff]
    tauto
  rw [sum_fibers (s \ V) B, sum_fibers (s \ (V \ B)) B, h₁, h₂, sum_mul, mul_sum]
  apply sum_le_sum
  intro t ht
  rw [allowed_sdiff, allowed_sdiff_outside]
  exact h t ht

/-- Multiplication, viewed as an embedding of vertices. -/
private def scale (a : ℕ) (ha : 0 < a) : ℕ ↪ ℕ :=
  ⟨(a * ·), fun _ _ h => (Nat.eq_of_mul_eq_mul_left ha h)⟩

private def block (a b : ℕ) (ha : 0 < a) := (below b).map (scale a ha)

private lemma mem_block {a b x : ℕ} {ha : 0 < a} :
    x ∈ block a b ha ↔ x ∈ below (a * b) ∧ a ∣ x := by
  rw [block, mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hy₁, hy₂⟩ := mem_below.mp hy
    exact ⟨mem_below.mpr ⟨Nat.mul_pos ha hy₁, Nat.mul_lt_mul_of_pos_left hy₂ ha⟩, ⟨y, rfl⟩⟩
  · rintro ⟨hx, y, rfl⟩
    obtain ⟨hx₁, hx₂⟩ := mem_below.mp hx
    exact ⟨y, mem_below.mpr ⟨by by_contra! h; simp_all [Nat.eq_zero_of_le_zero h],
      (Nat.mul_lt_mul_left ha).mp hx₂⟩, rfl⟩

private lemma count_scale (a : ℕ) (ha : 0 < a) (s : Finset ℕ) :
    count (s.map (scale a ha)) = count s := by
  symm
  refine card_bij (fun t _ => t.map (scale a ha)) ?_ ?_ ?_
  · intro t ht
    obtain ⟨hs, hp⟩ := mem_family.mp ht
    refine mem_family.mpr ⟨map_subset_map.mpr hs, ?_⟩
    intro x hx y hy hxy
    obtain ⟨u, hu, rfl⟩ := mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := mem_map.mp hy
    exact congrArg (scale a ha) (hp u hu v hv ((Nat.mul_dvd_mul_iff_left ha).mp hxy))
  · exact fun _ _ _ _ h => map_injective _ h
  · intro t ht
    obtain ⟨hs, hp⟩ := mem_family.mp ht
    obtain ⟨u, hus, he⟩ := subset_map_iff.mp hs
    refine ⟨u, mem_family.mpr ⟨hus, ?_⟩, he.symm⟩
    intro x hx y hy hxy
    have h : scale a ha x = scale a ha y :=
      hp _ (he.symm ▸ mem_map_of_mem _ hx) _ (he.symm ▸ mem_map_of_mem _ hy)
        ((Nat.mul_dvd_mul_iff_left ha).mpr hxy)
    exact (scale a ha).injective h

private lemma count_block (a b : ℕ) (ha : 0 < a) (V : Finset ℕ)
    (hV : ∀ x ∈ block a b ha, x ∈ V ↔ x ∣ a * b) :
    (∀ x ∈ below (a * b), x ∉ block a b ha → x ∉ V →
      ∀ y ∈ target b, ¬ x ∣ a * y) →
    count (below (a * b) \ V) * count (below b) ≤
      count (below b \ target b) * count (below (a * b) \ (V \ block a b ha)) := by
  intro hs
  apply conditional_count
  intro t ht
  let C : Finset ℕ := (below b).filter fun j => Compatible t (a * j)
  have ht' := (mem_family.mp ht).1
  have hout {x : ℕ} (hx : x ∈ t) :
      x ∈ below (a * b) ∧ x ∉ block a b ha ∧ x ∉ V := by
    simpa only [mem_sdiff, and_assoc] using ht' hx
  have hcompat {j : ℕ} (hj : j ∈ below b) :
      Compatible t (a * j) ↔ ∀ x ∈ t, ¬ x ∣ a * j := by
    refine ⟨fun h x hx => (h x hx).1, fun h x hx => ⟨h x hx, ?_⟩⟩
    intro hd
    exact (hout hx).2.1 (mem_block.mpr ⟨(hout hx).1, dvd_trans (dvd_mul_right a j) hd⟩)
  have hAC : target b ⊆ C := by
    intro j hj
    exact mem_filter.mpr ⟨(mem_target.mp hj).1,
      (hcompat (mem_target.mp hj).1).mpr (fun x hx => hs x (hout hx).1 (hout hx).2.1 (hout hx).2.2 j hj)⟩
  have hC : ∀ x ∈ below b, ∀ y ∈ C, x ∣ y → x ∈ C := by
    intro x hx y hy hd
    refine mem_filter.mpr ⟨hx, (hcompat hx).mpr ?_⟩
    intro z hz hz'
    obtain ⟨hyb, hc⟩ := mem_filter.mp hy
    exact (hcompat hyb).mp hc z hz (dvd_trans hz' ((Nat.mul_dvd_mul_iff_left ha).mpr hd))
  have hA : ∀ x ∈ below b, ∀ y ∈ target b, x ∣ y → x ∈ target b :=
    fun x hx y hy hd => mem_target.mpr ⟨hx, dvd_trans hd (mem_target.mp hy).2⟩
  have he : allowed (below (a * b)) (block a b ha) t = C.map (scale a ha) := by
    ext x
    simp only [mem_allowed, mem_map]
    constructor
    · rintro ⟨⟨_, hb⟩, hc⟩
      obtain ⟨j, hj, rfl⟩ := mem_map.mp hb
      exact ⟨j, mem_filter.mpr ⟨hj, hc⟩, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      have hb : scale a ha j ∈ block a b ha := mem_map_of_mem _ (mem_filter.mp hj).1
      exact ⟨⟨(mem_block.mp hb).1, hb⟩, (mem_filter.mp hj).2⟩
  have hev : allowed (below (a * b)) (block a b ha) t \ V =
      (C \ target b).map (scale a ha) := by
    rw [he]
    ext x
    simp only [mem_sdiff, mem_map]
    constructor
    · rintro ⟨⟨j, hj, rfl⟩, hv⟩
      have hb : scale a ha j ∈ block a b ha := mem_map_of_mem _ (mem_filter.mp hj).1
      refine ⟨j, ⟨hj, ?_⟩, rfl⟩
      intro htgt
      exact hv ((hV _ hb).mpr ((Nat.mul_dvd_mul_iff_left ha).mpr (mem_target.mp htgt).2))
    · rintro ⟨j, ⟨hj, htgt⟩, rfl⟩
      have hbelow := (mem_filter.mp hj).1
      have hb : scale a ha j ∈ block a b ha := mem_map_of_mem _ hbelow
      refine ⟨⟨j, hj, rfl⟩, ?_⟩
      intro hv
      exact htgt (mem_target.mpr ⟨hbelow, (Nat.mul_dvd_mul_iff_left ha).mp ((hV _ hb).mp hv)⟩)
  rw [hev, he, count_scale, count_scale]
  exact count_avoidance hAC (filter_subset _ _) hA hC

private lemma incomparable_blocks {a b : ℕ} {ha : 0 < a} {hb : 0 < b}
    (hc : Nat.Coprime a b) {x y : ℕ} (hx : x ∈ block a b ha) (hy : y ∈ block b a hb) :
    ¬ x ∣ y ∧ ¬ y ∣ x := by
  obtain ⟨hxp, hax⟩ := mem_block.mp hx
  obtain ⟨hyp, hby⟩ := mem_block.mp hy
  rw [Nat.mul_comm b a] at hyp
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact (mem_below.mp hyp).2.not_ge
      (Nat.le_of_dvd (mem_below.mp hyp).1 (hc.mul_dvd_of_dvd_of_dvd (dvd_trans hax h) hby))
  · exact (mem_below.mp hxp).2.not_ge
      (Nat.le_of_dvd (mem_below.mp hxp).1 (hc.mul_dvd_of_dvd_of_dvd hax (dvd_trans hby h)))

private lemma block_step (a b : ℕ) (ha : 0 < a) :
    count (below (a * b) \ target (a * b)) * count (below b) ≤
      count (below b \ target b) * count (below (a * b) \ (target (a * b) \ block a b ha)) := by
  apply count_block a b ha
  · intro x hx
    exact ⟨fun h => (mem_target.mp h).2, fun h => mem_target.mpr ⟨(mem_block.mp hx).1, h⟩⟩
  · intro x hx _ hV y hy hd
    exact hV (mem_target.mpr ⟨hx, dvd_trans hd
      ((Nat.mul_dvd_mul_iff_left ha).mpr (mem_target.mp hy).2)⟩)

private lemma second_step (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : Nat.Coprime a b) :
    count (below (a * b) \ (target (a * b) \ block a b ha)) * count (below a) ≤
      count (below a \ target a) * count (below (a * b)) := by
  rw [Nat.mul_comm a b]
  let V := target (b * a) \ block a b ha
  change count (below (b * a) \ V) * count (below a) ≤ _
  have h := count_block b a hb V ?_ ?_
  · exact h.trans (Nat.mul_le_mul_left _ (count_mono sdiff_subset))
  · intro x hx
    have hn : x ∉ block a b ha := fun hx' =>
      (incomparable_blocks hc hx' hx).1 (dvd_refl x)
    exact ⟨fun h => (mem_target.mp (mem_sdiff.mp h).1).2,
      fun h => mem_sdiff.mpr ⟨mem_target.mpr ⟨(mem_block.mp hx).1, h⟩, hn⟩⟩
  · intro x hx _ hxV y hy hxy
    have hxd : x ∈ target (b * a) := mem_target.mpr ⟨hx, dvd_trans hxy
      ((Nat.mul_dvd_mul_iff_left hb).mpr (mem_target.mp hy).2)⟩
    have hxB : x ∈ block a b ha := by
      by_contra hn
      exact hxV (mem_sdiff.mpr ⟨hxd, hn⟩)
    have hyB : b * y ∈ block b a hb := mem_map_of_mem _ (mem_target.mp hy).1
    exact (incomparable_blocks hc hxB hyB).1 hxy

private lemma ratio_step {l r b : Finset ℕ} {a : Finset ℕ}
    (h : count l * count b ≤ count a * count r) {s : Finset ℕ} :
    (count l : ℚ) / count s ≤ ((count a : ℚ) / count b) * ((count r : ℚ) / count s) := by
  have hb : (0 : ℚ) < count b := by exact_mod_cast count_pos b
  have hs : (0 : ℚ) < count s := by exact_mod_cast count_pos s
  rw [← mul_div_assoc, div_le_div_iff_of_pos_right hs, div_mul_eq_mul_div, le_div_iff₀ hb]
  exact_mod_cast h

/-- The one-block argument works for all positive factors. -/
lemma g_mul_le_right (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : g (a * b) ≤ g b := by
  rw [g_ratio (a * b) (Nat.mul_pos ha hb), g_ratio b hb]
  have h := (block_step a b ha).trans (Nat.mul_le_mul_left _ (count_mono sdiff_subset))
  have hs : (0 : ℚ) < count (below (a * b)) := by exact_mod_cast count_pos (below (a * b))
  have ht : (0 : ℚ) < count (below b) := by exact_mod_cast count_pos (below b)
  apply (div_le_div_iff₀ hs ht).mpr
  exact_mod_cast h

theorem mcnew_conj1 :
    (∀ n m : ℕ, 0 < n → 0 < m → Nat.Coprime n m → g (n * m) ≤ g n * g m) ∧
    (∀ p i : ℕ, p.Prime → g (p ^ (i + 1)) ≤ g (p ^ i)) := by
  constructor
  · intro n m hn hm hc
    have h₁ := ratio_step (s := below (n * m)) (block_step n m hn)
    have h₂ := ratio_step (s := below (n * m)) (second_step n m hn hm hc)
    rw [div_self (ne_of_gt (by exact_mod_cast count_pos (below (n * m)))), mul_one] at h₂
    rw [← g_ratio (n * m) (Nat.mul_pos hn hm), ← g_ratio m hm] at h₁
    rw [← g_ratio n hn] at h₂
    exact h₁.trans ((mul_le_mul_of_nonneg_left h₂ (g_nonneg m hm)).trans_eq (mul_comm _ _))
  · intro p i hp
    rw [pow_succ']
    exact g_mul_le_right p (p ^ i) hp.pos (pow_pos hp.pos _)

#check mcnew_conj1
#print axioms mcnew_conj1
#print axioms g_mul_le_right

end PrimitiveRatio
```
