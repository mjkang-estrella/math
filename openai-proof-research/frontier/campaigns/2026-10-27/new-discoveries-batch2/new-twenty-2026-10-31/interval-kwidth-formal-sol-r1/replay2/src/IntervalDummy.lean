import IntervalMatching

namespace IntervalWidth
variable {α : Type*} [LE α] {n k d : Nat} {I : Fin n → Interval α}

/-- A saturating injection to real supply copies plus d universal dummy supplies. -/
structure DummyMatching (k d : Nat) (I : Fin n → Interval α) where
  assign : Fin n → (Fin n × Fin k) ⊕ Fin d
  injective : Function.Injective assign
  edge : ∀ j i s, assign j = Sum.inl (i,s) → Compatible I i j

def DummyMatching.parent (D : DummyMatching k d I) (j : Fin n) : Option (Fin n) :=
  match D.assign j with
  | Sum.inl c => some c.1
  | Sum.inr _ => none

theorem DummyMatching.copy_exists (D : DummyMatching k d I) (i j : Fin n)
    (h : D.parent j = some i) : ∃ s, D.assign j = Sum.inl (i,s) := by
  cases e : D.assign j with
  | inl c =>
    have hi : c.1 = i := Option.some.inj (by simpa [parent, e] using h)
    exact ⟨c.2, by rw [← hi]⟩
  | inr c => simp [parent, e] at h

theorem DummyMatching.dummy_exists (D : DummyMatching k d I) (j : Fin n)
    (h : D.parent j = none) : ∃ s, D.assign j = Sum.inr s := by
  cases e : D.assign j with
  | inl c => simp [parent, e] at h
  | inr c => exact ⟨c, rfl⟩

noncomputable def DummyMatching.toMatching (D : DummyMatching k d I) :
    CopyMatching k I where
  parent := D.parent
  edge := by
    intro i j h
    obtain ⟨s, hs⟩ := D.copy_exists i j h
    exact D.edge j i s hs
  slots := fun i => {
    toFun := fun j => Classical.choose (D.copy_exists i j.val j.property)
    inj' := by
      intro a b h
      apply Subtype.ext
      apply D.injective
      exact (Classical.choose_spec (D.copy_exists i a.val a.property)).trans
        ((congrArg (fun s : Fin k => Sum.inl (i,s)) h).trans
          (Classical.choose_spec (D.copy_exists i b.val b.property)).symm) }

theorem DummyMatching.root_bound (D : DummyMatching k d I) :
    D.toMatching.toForest.rootCount ≤ d := by
  classical
  let f : D.toMatching.toForest.Roots → Fin d := fun j =>
    Classical.choose (D.dummy_exists j.val j.property)
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply D.injective
    exact (Classical.choose_spec (D.dummy_exists a.val a.property)).trans
      ((congrArg Sum.inr h).trans
        (Classical.choose_spec (D.dummy_exists b.val b.property)).symm)
  exact (Fintype.card_le_of_injective f hf).trans_eq (Fintype.card_fin d)

theorem DummyMatching.width_le (D : DummyMatching k d I) : width k I ≤ d :=
  (width_le_roots D.toMatching.toForest).trans D.root_bound

end IntervalWidth
