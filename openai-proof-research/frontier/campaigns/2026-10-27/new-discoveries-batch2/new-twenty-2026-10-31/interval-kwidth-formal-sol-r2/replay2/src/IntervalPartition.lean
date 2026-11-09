import IntervalForest
import Mathlib.Data.Fintype.EquivFin

namespace IntervalWidth
variable {α : Type*} [LE α] {n k : Nat} {I : Fin n → Interval α}

abbrev Forest.Roots (F : Forest k I) := {j : Fin n // F.parent j = none}

noncomputable def Forest.rootCount (F : Forest k I) : Nat := by
  classical
  exact Fintype.card F.Roots

/-- Each chronological parent forest gives its genuine rooted tree partition. -/
noncomputable def Forest.toPartition (F : Forest k I) :
    HeapPartition k I F.rootCount := by
  classical
  let e : F.Roots ≃ Fin F.rootCount := Fintype.equivFin F.Roots
  let a : Fin n → F.Roots := fun j => ⟨F.rootAt j, F.rootAt_none j⟩
  refine {
    color := fun j => e (a j)
    root := fun c => (e.symm c).val
    root_color := ?_
    parent := F.parent
    root_parent := fun c => (e.symm c).property
    parent_color := ?_
    edge := F.edge
    arity := F.arity
    rooted := ?_ }
  · intro c
    have h : a (e.symm c).val = e.symm c := by
      apply Subtype.ext
      exact F.rootAt_of_none _ (e.symm c).property
    change e (a (e.symm c).val) = c
    rw [h, e.apply_symm_apply]
  · intro i j h
    exact congrArg e (Subtype.ext (F.rootAt_parent i j h))
  · intro j
    rw [e.symm_apply_apply]
    exact F.rootAt_path j

theorem width_le_roots (F : Forest k I) : width k I ≤ F.rootCount :=
  width_le F.toPartition

/-- The roots of a tree partition are exactly its class representatives. -/
noncomputable def HeapPartition.rootsEquiv {r : Nat} (P : HeapPartition k I r) :
    P.toForest.Roots ≃ Fin r where
  toFun := fun j => P.color j.val
  invFun := fun c => ⟨P.root c, P.root_parent c⟩
  left_inv := by
    intro j
    apply Subtype.ext
    exact ((parent_none_iff_root P j.val).mp j.property).symm
  right_inv := P.root_color

theorem HeapPartition.rootCount_eq {r : Nat} (P : HeapPartition k I r) :
    P.toForest.rootCount = r := by
  classical
  exact (Fintype.card_congr P.rootsEquiv).trans (Fintype.card_fin r)

/-- Exact optimization over forests, derived from the tree-partition definition. -/
theorem width_eq_min_roots (k : Nat) (I : Fin n → Interval α) :
    (∃ F : Forest k I, F.rootCount = width k I) ∧
    (∀ F : Forest k I, width k I ≤ F.rootCount) := by
  obtain ⟨P⟩ := width_attained k I
  exact ⟨⟨P.toForest, P.rootCount_eq⟩, width_le_roots⟩

end IntervalWidth
