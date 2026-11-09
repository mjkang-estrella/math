import CodeLoopSpace
import Mathlib.Data.Multiset.Sort

noncomputable section

abbrev Label := {a : W4 // a ≠ 0} ⊕ B3

theorem mult_pos (i : Fin 2) (a : W4) : 0 < mult i a := by
  unfold mult; split <;> decide

def labelSection (i : Fin 2) : Label → Dcoord i
  | Sum.inl a => Sum.inl ⟨a,⟨0,mult_pos i a⟩⟩
  | Sum.inr b => Sum.inr b

theorem labelSection_right (i : Fin 2) (a : Label) : columnLabel i (labelSection i a) = a := by
  cases a <;> rfl

def binaryCodeSetoid {α : Type} (V : Submodule (ZMod 2) (α → ZMod 2)) : Setoid α where
  r c d := ∀ v ∈ V, v c = v d
  iseqv := ⟨fun _ _ _ => rfl, fun h v hv => (h v hv).symm,
    fun h k v hv => (h v hv).trans (k v hv)⟩

def coordinateSetoid (i : Fin 2) : Setoid (Dcoord i) := binaryCodeSetoid (D i)

abbrev ColumnClass (i : Fin 2) := Quotient (coordinateSetoid i)

def classLabel (i : Fin 2) : ColumnClass i → Label :=
  Quotient.lift (columnLabel i) (fun c d h => (sameColumn_iff i c d).mp h)

def classLabelEquiv (i : Fin 2) : ColumnClass i ≃ Label where
  toFun := classLabel i
  invFun a := Quotient.mk _ (labelSection i a)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ c =>
      apply Quotient.sound
      apply (sameColumn_iff i _ _).mpr
      exact labelSection_right i (columnLabel i c)
  right_inv := labelSection_right i

noncomputable instance columnClassFintype (i : Fin 2) : Fintype (ColumnClass i) :=
  Fintype.ofEquiv Label (classLabelEquiv i).symm

/-- The actual coordinates belonging to a quotient class. -/
def ClassPositions (i : Fin 2) (q : ColumnClass i) :=
  {c : Dcoord i // Quotient.mk (coordinateSetoid i) c = q}

noncomputable instance classPositionsFintype (i : Fin 2) (q : ColumnClass i) : Fintype (ClassPositions i q) :=
  by
    classical
    unfold ClassPositions
    infer_instance

def labelMultiplicity (i : Fin 2) : Label → Nat
  | Sum.inl a => mult i a
  | Sum.inr _ => 1

def positionFiberEquiv (i : Fin 2) (q : ColumnClass i) :
    ClassPositions i q ≃ {c : Dcoord i // columnLabel i c = classLabel i q} where
  toFun c := ⟨c.val, congrArg (classLabel i) c.property⟩
  invFun c := ⟨c.val, (classLabelEquiv i).injective c.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def labelFiberCopies (i : Fin 2) (a : Label) :
    {c : Dcoord i // columnLabel i c = a} ≃ Fin (labelMultiplicity i a) := by
  cases a with
  | inl a =>
    refine
      { toFun := fun c => ?_
        invFun := fun t => ⟨Sum.inl ⟨a,t⟩,rfl⟩
        left_inv := ?_
        right_inv := ?_ }
    · rcases c with ⟨c,h⟩
      cases c with
      | inl c =>
        have he : c.1 = a := Sum.inl.inj h
        exact he ▸ c.2
      | inr b => simp [columnLabel] at h
    · rintro ⟨c,h⟩
      cases c with
      | inl c =>
        rcases c with ⟨b,t⟩
        have he : b = a := Sum.inl.inj h
        subst a
        rfl
      | inr b => simp [columnLabel] at h
    · intro t; rfl
  | inr b =>
    change {c : Dcoord i // columnLabel i c = Sum.inr b} ≃ Fin 1
    refine
      { toFun := fun _ => 0
        invFun := fun _ => ⟨Sum.inr b,rfl⟩
        left_inv := ?_
        right_inv := fun t => Subsingleton.elim _ _ }
    rintro ⟨c,h⟩
    cases c with
    | inl c => simp [columnLabel] at h
    | inr c =>
      have he : c = b := Sum.inr.inj h
      subst b
      rfl

theorem classPositions_card (i : Fin 2) (q : ColumnClass i) :
    Fintype.card (ClassPositions i q) = labelMultiplicity i (classLabel i q) := by
  rw [Fintype.card_congr ((positionFiberEquiv i q).trans
    (labelFiberCopies i (classLabel i q))),Fintype.card_fin]

theorem D_reduced (i : Fin 2) (q : ColumnClass i) :
    Fintype.card (ClassPositions i q) < 8 := by
  rw [classPositions_card]
  cases classLabel i q with
  | inl a => change mult i a < 8; unfold mult; split <;> decide
  | inr b => change 1 < 8; decide


def binaryClassPositions {α : Type} (V : Submodule (ZMod 2) (α → ZMod 2))
    (q : Quotient (binaryCodeSetoid V)) := {c : α // Quotient.mk (binaryCodeSetoid V) c = q}

noncomputable def binaryCodeType {α : Type} (V : Submodule (ZMod 2) (α → ZMod 2))
    (qFin : Fintype (Quotient (binaryCodeSetoid V)))
    (pFin : ∀ q, Fintype (binaryClassPositions V q)) : Multiset Nat :=
  @Finset.univ _ qFin |>.val.map (fun q => @Fintype.card _ (pFin q))

noncomputable def codeType (i : Fin 2) : Multiset Nat :=
  Finset.univ.val.map (fun q : ColumnClass i => Fintype.card (ClassPositions i q))

noncomputable def labelType (i : Fin 2) : Multiset Nat :=
  Finset.univ.val.map (labelMultiplicity i)

theorem codeType_eq_labelType (i : Fin 2) : codeType i = labelType i := by
  classical
  unfold codeType labelType
  simp_rw [classPositions_card]
  have h : Finset.univ.val.map (classLabel i) = (Finset.univ : Finset Label).val := by
    have he : (Finset.univ : Finset (ColumnClass i)).map
        (classLabelEquiv i).toEmbedding = Finset.univ := by
      ext a
      simp
    exact congrArg Finset.val he
  rw [← h,Multiset.map_map]
  rfl


theorem multiset_two_values {α : Type*} [DecidableEq α] (s : Finset α)
    (p : α → Prop) [DecidablePred p] :
    s.val.map (fun a => if p a then (5:Nat) else 1) =
      Multiset.replicate (s.filter p).card 5 +
      Multiset.replicate (s.filter fun a => ¬ p a).card 1 := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    by_cases hp : p a
    · simp [Finset.filter_insert,ha,hp,ih,Multiset.replicate_succ]
    · simp [Finset.filter_insert,ha,hp,ih,Multiset.replicate_succ,Multiset.add_cons]

def richLabel (i : Fin 2) : Label → Prop
  | Sum.inl a => a.val ∈ HofI i
  | Sum.inr _ => False

instance (i : Fin 2) : DecidablePred (richLabel i) := fun a => by
  cases a <;> unfold richLabel <;> infer_instance

theorem rich_card (i : Fin 2) : (Finset.univ.filter (richLabel i)).card = 7 := by
  classical
  rw [← HofI_card i]
  apply Finset.card_bij (fun a _ => match a with | Sum.inl a => a.val | Sum.inr _ => 0)
  · intro a ha
    cases a with
    | inl a => exact (Finset.mem_filter.mp ha).2
    | inr b => exact ((Finset.mem_filter.mp ha).2 : False).elim
  · intro a ha b hb he
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Subtype.ext he)
      | inr b => exact ((Finset.mem_filter.mp hb).2 : False).elim
    | inr a => exact ((Finset.mem_filter.mp ha).2 : False).elim
  · intro a ha
    exact ⟨Sum.inl ⟨a,HofI_ne_zero ha⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩,rfl⟩

theorem label_card : Fintype.card Label = 22 := by
  have h := Fintype.card_congr (Equiv.sumCompl fun x : W4 => x = 0)
  simp only [Fintype.card_sum,Fintype.card_subtype_eq,card_W4] at h
  change 1 + Fintype.card {x : W4 // x ≠ 0} = 16 at h
  have h15 : Fintype.card {x : W4 // x ≠ 0} = 15 := by omega
  rw [Fintype.card_sum,h15,B3_card]

theorem exact_codeType (i : Fin 2) : codeType i =
    Multiset.replicate 15 1 + Multiset.replicate 7 5 := by
  classical
  rw [codeType_eq_labelType]
  have hf : labelMultiplicity i = fun a => if richLabel i a then 5 else 1 := by
    funext a; cases a <;> rfl
  unfold labelType
  rw [hf,multiset_two_values,rich_card]
  have hn : (Finset.univ.filter fun a => ¬richLabel i a).card = 15 := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Label))
      (p := richLabel i)
    rw [rich_card,Finset.card_univ,label_card] at h
    omega
  rw [hn,add_comm]


noncomputable def sortedCodeType (i : Fin 2) : List Nat := (codeType i).sort (· ≤ ·)

theorem exact_sortedCodeType (i : Fin 2) : sortedCodeType i =
    List.replicate 15 1 ++ List.replicate 7 5 := by
  unfold sortedCodeType
  rw [exact_codeType]
  have hm : Multiset.replicate 15 (1:Nat) + Multiset.replicate 7 5 =
      ((List.replicate 15 1 ++ List.replicate 7 5 : List Nat) : Multiset Nat) := by rfl
  rw [hm,Multiset.coe_sort]
  apply List.mergeSort_eq_self
  decide +kernel
