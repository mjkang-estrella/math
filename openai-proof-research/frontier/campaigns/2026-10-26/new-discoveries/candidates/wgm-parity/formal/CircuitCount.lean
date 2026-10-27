import CircuitReach

namespace WGMParity

noncomputable def reachableEquiv {L I : Type*} (root : I)
    (child : I × Bool → L ⊕ I)
    (hl : ∀ j : L, CircuitReach root child (Sum.inl j)) :
    {v : L ⊕ I // CircuitReach root child v} ≃
      L ⊕ {i : I // CircuitReach root child (Sum.inr i)} where
  toFun v := match v with
    | ⟨Sum.inl j, _⟩ => Sum.inl j
    | ⟨Sum.inr i, hi⟩ => Sum.inr ⟨i, hi⟩
  invFun v := match v with
    | Sum.inl j => ⟨Sum.inl j, hl j⟩
    | Sum.inr i => ⟨Sum.inr i.1, i.2⟩
  left_inv := by rintro ⟨v, hv⟩; cases v <;> rfl
  right_inv := by intro v; cases v <;> rfl

theorem reachable_count_bound {L I : Type*} [Fintype L] [Fintype I]
    (root : I) (child : I × Bool → L ⊕ I)
    (hl : ∀ j : L, CircuitReach root child (Sum.inl j)) :
    Fintype.card L ≤ Nat.card {i : I // CircuitReach root child (Sum.inr i)} + 1 := by
  classical
  let RI := {i : I // CircuitReach root child (Sum.inr i)}
  let RV := {v : L ⊕ I // CircuitReach root child v}
  let f : (RI × Bool) ⊕ Unit → RV := Sum.elim
    (fun p => ⟨child (p.1.1, p.2), circuitReach_child root child p.1.2 p.2⟩)
    (fun _ => ⟨Sum.inr root, circuitReach_root root child⟩)
  have hf : Function.Surjective f := by
    intro v
    rcases circuitReach_last root child v.2 with h | ⟨i, b, hi, hc⟩
    · exact ⟨Sum.inr (), Subtype.ext h.symm⟩
    · exact ⟨Sum.inl (⟨i, hi⟩, b), Subtype.ext hc⟩
  have hb := Fintype.card_le_of_surjective f hf
  have he := Fintype.card_congr (reachableEquiv root child hl)
  change Fintype.card RV = Fintype.card (L ⊕ RI) at he
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_unit] at hb he
  rw [Nat.card_eq_fintype_card]
  change Fintype.card L ≤ Fintype.card RI + 1
  omega

theorem equality_count_reaches_all {L I : Type*} [Fintype L] [Fintype I]
    (root : I) (child : I × Bool → L ⊕ I)
    (hl : ∀ j : L, CircuitReach root child (Sum.inl j))
    (hsize : Fintype.card I + 1 = Fintype.card L) :
    ∀ v, CircuitReach root child v := by
  classical
  have hb := reachable_count_bound root child hl
  rw [Nat.card_eq_fintype_card] at hb
  have hi : ∀ i : I, CircuitReach root child (Sum.inr i) := by
    intro i
    by_contra hn
    have hh := Fintype.card_subtype_lt
      (p := fun k : I => CircuitReach root child (Sum.inr k)) (x := i) hn
    omega
  intro v
  cases v with
  | inl j => exact hl j
  | inr i => exact hi i

theorem equality_count_augmented_bijective {L I : Type*} [Fintype L] [Fintype I]
    (root : I) (child : I × Bool → L ⊕ I)
    (hl : ∀ j : L, CircuitReach root child (Sum.inl j))
    (hsize : Fintype.card I + 1 = Fintype.card L) :
    Function.Bijective (Sum.elim child (fun _ : Unit => Sum.inr root)) := by
  classical
  let f : (I × Bool) ⊕ Unit → L ⊕ I := Sum.elim child (fun _ => Sum.inr root)
  have hf : Function.Surjective f := by
    intro v
    have hv := equality_count_reaches_all root child hl hsize v
    rcases circuitReach_last root child hv with h | ⟨i, b, _, hc⟩
    · exact ⟨Sum.inr (), h.symm⟩
    · exact ⟨Sum.inl (i, b), hc⟩
  have hcard : Fintype.card ((I × Bool) ⊕ Unit) = Fintype.card (L ⊕ I) := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, Fintype.card_unit]
    omega
  exact ⟨(Fintype.bijective_iff_surjective_and_card f).mpr ⟨hf, hcard⟩ |>.1, hf⟩

theorem equality_count_input_injective {L I : Type*} [Fintype L] [Fintype I]
    (root : I) (child : I × Bool → L ⊕ I)
    (hl : ∀ j : L, CircuitReach root child (Sum.inl j))
    (hsize : Fintype.card I + 1 = Fintype.card L) : Function.Injective child := by
  intro p q hpq
  have hf := (equality_count_augmented_bijective root child hl hsize).1
  exact Sum.inl_injective (hf (show Sum.elim child (fun _ : Unit => Sum.inr root)
    (Sum.inl p) = Sum.elim child (fun _ : Unit => Sum.inr root) (Sum.inl q) from hpq))

theorem equality_count_root_not_input {L I : Type*} [Fintype L] [Fintype I]
    (root : I) (child : I × Bool → L ⊕ I)
    (hl : ∀ j : L, CircuitReach root child (Sum.inl j))
    (hsize : Fintype.card I + 1 = Fintype.card L) :
    ∀ p, child p ≠ Sum.inr root := by
  intro p hp
  have hf := (equality_count_augmented_bijective root child hl hsize).1
  have hh := hf (show Sum.elim child (fun _ : Unit => Sum.inr root)
    (Sum.inl p) = Sum.elim child (fun _ : Unit => Sum.inr root) (Sum.inr ()) from hp)
  cases hh

end WGMParity
