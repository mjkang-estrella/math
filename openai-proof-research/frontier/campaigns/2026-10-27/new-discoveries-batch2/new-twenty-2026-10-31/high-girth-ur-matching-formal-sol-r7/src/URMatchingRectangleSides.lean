module
public import URMatchingEmbeddedSwitch
@[expose] public section
namespace URMatching
universe v
variable {V : Type v}

/-- Last floor(m/2) matched left endpoints and first floor(m/2) matched right
endpoints form an empty rectangle in any topological indexing. This lemma does
not assume the original matching is perfect in the ambient graph. -/
theorem ordered_empty_rectangle_sides (m : ℕ) (G : SimpleGraph V) (e : Sum (Fin m) (Fin m) ↪ V)
    (forward : ∀ i j : Fin m, i ≠ j →
      G.Adj (e (Sum.inl i)) (e (Sum.inr j)) → i.val < j.val) :
    ∃ A B : Finset V, A.card = m / 2 ∧ B.card = m / 2 ∧
      (∀ x ∈ A, ∃ i, x = e (Sum.inl i)) ∧
      (∀ y ∈ B, ∃ i, y = e (Sum.inr i)) ∧
      Disjoint A B ∧ ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y := by
  classical
  let s := m / 2
  have hs : s ≤ m := Nat.div_le_self m 2
  let a : Fin s → V := fun i => e (Sum.inl ⟨m - s + i.val, by omega⟩)
  let b : Fin s → V := fun i => e (Sum.inr ⟨i.val, by omega⟩)
  have ha : Function.Injective a := by
    intro i j h
    have hh := Fin.val_eq_of_eq (Sum.inl.inj (e.injective h))
    apply Fin.ext
    dsimp at hh
    omega
  have hb : Function.Injective b := by
    intro i j h
    have hh := Fin.val_eq_of_eq (Sum.inr.inj (e.injective h))
    apply Fin.ext
    exact hh
  refine ⟨Finset.univ.image a, Finset.univ.image b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ ha, Finset.card_univ, Fintype.card_fin]
  · rw [Finset.card_image_of_injective _ hb, Finset.card_univ, Fintype.card_fin]
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨_, rfl⟩
  · intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨_, rfl⟩
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hy
    have h := e.injective hj
    cases h
  · intro x hx y hy hxy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    have hne : (⟨m - s + i.val, by omega⟩ : Fin m) ≠ ⟨j.val, by omega⟩ := by
      intro h
      have := Fin.val_eq_of_eq h
      dsimp at this
      omega
    have hh := forward _ _ hne hxy
    dsimp at hh
    omega
end URMatching
