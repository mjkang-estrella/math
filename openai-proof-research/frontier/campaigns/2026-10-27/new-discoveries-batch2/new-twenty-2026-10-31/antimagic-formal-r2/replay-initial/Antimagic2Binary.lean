import Antimagic2Star
namespace Antimagic
open Finset

/-- Source Figure 5, indexed by the six actual incoming endpoints. -/
def binaryMap : Nonroot 2 2 → Fin 6 := fun a =>
  ⟨label 2 2 a.val.1.val a.val.2.val - 1, by
    have h : ∀ a : Nonroot 2 2, label 2 2 a.val.1.val a.val.2.val - 1 < 6 := by decide
    exact h a⟩

noncomputable def binaryEquiv : Nonroot 2 2 ≃ Fin 6 :=
  Equiv.ofBijective binaryMap (by decide)

noncomputable def binaryLabeling : Labeling (tree 2 2) :=
  (incomingEquiv (by decide : 0 < 2)).symm.trans (binaryEquiv.trans
    (finCongr (by rw [← Fintype.card_congr (incomingEquiv (by decide : 0 < 2)),
      Fintype.card_congr binaryEquiv, Fintype.card_fin])))

theorem binary_label (a : Nonroot 2 2) :
    (binaryLabeling (incomingEdge (by decide) a)).val + 1 =
      label 2 2 a.val.1.val a.val.2.val := by
  change (binaryLabeling ((incomingEquiv (by decide)) a)).val + 1 = _
  simp only [binaryLabeling, Equiv.trans_apply, Equiv.symm_apply_apply,
    finCongr_apply, Fin.val_cast]
  change (label 2 2 a.val.1.val a.val.2.val - 1) + 1 = _
  have h : ∀ a : Nonroot 2 2, 1 ≤ label 2 2 a.val.1.val a.val.2.val := by decide
  exact Nat.sub_add_cancel (h a)

def binaryWeight (v : Vertex 2 2) : ℕ := ∑ a : Nonroot 2 2,
  if v = parent (by decide) a ∨ v = a.val then label 2 2 a.val.1.val a.val.2.val else 0

theorem binary_weight (v : Vertex 2 2) :
    weight (tree 2 2) binaryLabeling v = binaryWeight v := by
  rw [weight_incoming (by decide)]
  apply sum_congr rfl
  intro a _
  rw [binary_label]

theorem binary_construction :
    ∃ f : Labeling (tree 2 2),
      (∀ (u v : Vertex 2 2) (h : Child u v),
        (f ⟨s(u, v), (tree 2 2).mem_edgeSet.mpr (Or.inl h)⟩).val + 1 =
          label 2 2 v.1.val v.2.val) ∧
      IsLocal (tree 2 2) f ∧ colorCount (tree 2 2) f = 2 ^ 2 + 1 := by
  refine ⟨binaryLabeling, ?_, ?_, ?_⟩
  · intro u v h
    let a : Nonroot 2 2 := ⟨v, by have := h.1; unfold depth; omega⟩
    have he : (⟨s(u, v), (tree 2 2).mem_edgeSet.mpr (Or.inl h)⟩ : (tree 2 2).edgeSet) = incomingEdge (by decide) a := by
      apply Subtype.ext
      change s(u, v) = s(parent (by decide) a, v)
      rw [← child_parent_unique h (by decide)]
    rw [he]
    exact binary_label a
  · intro u v h
    rw [binary_weight, binary_weight]
    have hc : ∀ u v : Vertex 2 2, (tree 2 2).Adj u v → binaryWeight u ≠ binaryWeight v := by decide
    exact hc u v h
  · unfold colorCount
    rw [show weight (tree 2 2) binaryLabeling = binaryWeight from funext binary_weight]
    decide

#print axioms binary_construction
end Antimagic
