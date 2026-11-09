import IntervalMinimum

namespace IntervalWidth
variable {α : Type*} [LE α] {n k : Nat} {I : Fin n → Interval α}

/-- A chronological parent forest; it does not carry a partition or a root count. -/
structure Forest (k : Nat) (I : Fin n → Interval α) where
  parent : Fin n → Option (Fin n)
  edge : ∀ i j, parent j = some i → Compatible I i j
  arity : ∀ i, (Finset.univ.filter (fun j => parent j = some i)).card ≤ k

/-- Strict time makes following parents terminate. -/
theorem Forest.root_exists (F : Forest k I) (j : Fin n) :
    ∃ a, F.parent a = none ∧ Path F.parent a j := by
  have aux : ∀ t, ∀ j : Fin n, j.val = t →
      ∃ a, F.parent a = none ∧ Path F.parent a j := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro j hj
      cases e : F.parent j with
      | none => exact ⟨j, e, Path.refl j⟩
      | some i =>
        have hij : i.val < t := hj ▸ (F.edge i j e).1
        obtain ⟨a, ha, hp⟩ := ih i.val hij i rfl
        exact ⟨a, ha, Path.step hp e⟩
  exact aux j.val j rfl

theorem Path.root_unique {p : Fin n → Option (Fin n)} {a b j : Fin n}
    (ha : p a = none) (hb : p b = none)
    (h : Path p a j) (h' : Path p b j) : a = b := by
  induction h with
  | refl => exact (Path.to_root h' ha).symm
  | @step i j _ e ih =>
    cases h' with
    | refl => simp [hb] at e
    | @step t _ ht et =>
      have eq : t = i := Option.some.inj (et.symm.trans e)
      subst t
      exact ih ht

noncomputable def Forest.rootAt (F : Forest k I) (j : Fin n) : Fin n :=
  Classical.choose (F.root_exists j)

theorem Forest.rootAt_none (F : Forest k I) (j : Fin n) :
    F.parent (F.rootAt j) = none := (Classical.choose_spec (F.root_exists j)).1

theorem Forest.rootAt_path (F : Forest k I) (j : Fin n) :
    Path F.parent (F.rootAt j) j := (Classical.choose_spec (F.root_exists j)).2

theorem Forest.rootAt_of_none (F : Forest k I) (j : Fin n) (hj : F.parent j = none) :
    F.rootAt j = j := Path.to_root (F.rootAt_path j) hj

theorem Forest.rootAt_parent (F : Forest k I) (i j : Fin n)
    (h : F.parent j = some i) : F.rootAt i = F.rootAt j :=
  Path.root_unique (F.rootAt_none i) (F.rootAt_none j)
    (Path.step (F.rootAt_path i) h) (F.rootAt_path j)

/-- Forgetting tree class labels preserves the chronological parent forest. -/
def HeapPartition.toForest {r : Nat} (P : HeapPartition k I r) : Forest k I :=
  ⟨P.parent, P.edge, P.arity⟩

end IntervalWidth
