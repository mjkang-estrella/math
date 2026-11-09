import IntervalHallUpper

namespace IntervalWidth
variable {α : Type*} [LE α] {n k r : Nat} {I : Fin n → Interval α}

noncomputable def HeapPartition.saturate (P : HeapPartition k I r) :
    DummyMatching k r I := by
  classical
  let M := P.toForest.toMatching
  let f : Fin n → (Fin n × Fin k) ⊕ Fin r := fun j =>
    match h : P.parent j with
    | none => Sum.inr (P.color j)
    | some i => Sum.inl (i, M.slots i ⟨j,h⟩)
  have fnone (j : Fin n) (h : P.parent j = none) : f j = Sum.inr (P.color j) := by
    dsimp only [f]
    split <;> simp_all
  have fsome (j i : Fin n) (h : P.parent j = some i) :
      f j = Sum.inl (i, M.slots i ⟨j,h⟩) := by
    dsimp only [f]
    split
    · rename_i e; simp [h] at e
    · rename_i a ea
      have hi : a = i := Option.some.inj (ea.symm.trans h)
      subst a
      rfl
  refine ⟨f, ?_, ?_⟩
  · intro a b hab
    cases ea : P.parent a with
    | none =>
      rw [fnone a ea] at hab
      cases eb : P.parent b with
      | none =>
        rw [fnone b eb] at hab
        have hc := Sum.inr.inj hab
        rw [(parent_none_iff_root P a).mp ea, (parent_none_iff_root P b).mp eb, hc]
      | some j => rw [fsome b j eb] at hab; cases hab
    | some i =>
      rw [fsome a i ea] at hab
      cases eb : P.parent b with
      | none => rw [fnone b eb] at hab; cases hab
      | some j =>
        rw [fsome b j eb] at hab
        have hp := Sum.inl.inj hab
        have hij : i = j := congrArg Prod.fst hp
        subst j
        have hs := congrArg Prod.snd hp
        exact congrArg Subtype.val ((M.slots i).injective hs)
  · intro j i s h
    cases e : P.parent j with
    | none => rw [fnone j e] at h; cases h
    | some a =>
      rw [fsome j a e] at h
      have ha : a = i := congrArg Prod.fst (Sum.inl.inj h)
      subst a
      exact P.edge i j e

/-- Necessity of every finite Hall inequality, including the empty cut. -/
theorem DummyMatching.hall_bound {d : Nat} (D : DummyMatching k d I)
    (S : Finset (Fin n)) :
    S.card ≤ (S.biUnion (copyNeighbors k I)).card + d := by
  classical
  let T := (S.biUnion (copyNeighbors k I)).disjSum (Finset.univ : Finset (Fin d))
  have sub : S.image D.assign ⊆ T := by
    intro c hc
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
    cases e : D.assign j with
    | inl c =>
      have he := D.edge j c.1 c.2 e
      simp only [T, Finset.mem_disjSum, Finset.mem_biUnion]
      exact Or.inl ⟨c, ⟨j, hj, by simpa [copyNeighbors] using he⟩, rfl⟩
    | inr c => simp [T]
  have h := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ D.injective] at h
  simpa [T, Finset.card_disjSum] using h

theorem hall_bound_width (k : Nat) (I : Fin n → Interval α) (S : Finset (Fin n)) :
    S.card ≤ (S.biUnion (copyNeighbors k I)).card + width k I := by
  obtain ⟨P⟩ := width_attained k I
  exact P.saturate.hall_bound S

/-- Exact finite Hall characterization of the source tree-partition minimum. -/
theorem width_le_iff_hall (k d : Nat) (I : Fin n → Interval α) :
    width k I ≤ d ↔
      ∀ S : Finset (Fin n), S.card ≤ (S.biUnion (copyNeighbors k I)).card + d := by
  constructor
  · intro h S
    exact (hall_bound_width k I S).trans (Nat.add_le_add_left h _)
  · exact width_le_of_hall k d I

end IntervalWidth
