import Antimagic2Binary
namespace Antimagic
open Finset

def formulaWeight (t n : ℕ) (ht : 0 < t) (v : Vertex t n) : ℕ :=
  ∑ a : Nonroot t n, if v = parent ht a ∨ v = a.val then
    label t n a.val.1.val a.val.2.val else 0

/-- A finite certificate for the exact formula on actual incoming edges. -/
structure FiniteCertificate (t n m : ℕ) (ht : 0 < t) : Prop where
  positive : ∀ a : Nonroot t n, 1 ≤ label t n a.val.1.val a.val.2.val
  bounded : ∀ a : Nonroot t n, label t n a.val.1.val a.val.2.val - 1 < m
  bijective : Function.Bijective (fun a : Nonroot t n =>
    (⟨label t n a.val.1.val a.val.2.val - 1, bounded a⟩ : Fin m))
  proper : ∀ u v : Vertex t n, (tree t n).Adj u v →
    formulaWeight t n ht u ≠ formulaWeight t n ht v
  colors : (univ.image (formulaWeight t n ht)).card = t ^ n + 1

noncomputable def certifiedLabeling {t n m : ℕ} {ht : 0 < t}
    (c : FiniteCertificate t n m ht) : Labeling (tree t n) :=
  let e : Nonroot t n ≃ Fin m := Equiv.ofBijective _ c.bijective
  (incomingEquiv ht).symm.trans (e.trans
    (finCongr (by rw [← Fintype.card_congr (incomingEquiv ht),
      Fintype.card_congr e, Fintype.card_fin])))

theorem certified_label {t n m : ℕ} {ht : 0 < t}
    (c : FiniteCertificate t n m ht) (a : Nonroot t n) :
    (certifiedLabeling c (incomingEdge ht a)).val + 1 =
      label t n a.val.1.val a.val.2.val := by
  change (certifiedLabeling c ((incomingEquiv ht) a)).val + 1 = _
  simp only [certifiedLabeling, Equiv.trans_apply, Equiv.symm_apply_apply,
    finCongr_apply, Fin.val_cast]
  exact Nat.sub_add_cancel (c.positive a)

theorem certified_weight {t n m : ℕ} {ht : 0 < t}
    (c : FiniteCertificate t n m ht) (v : Vertex t n) :
    weight (tree t n) (certifiedLabeling c) v = formulaWeight t n ht v := by
  rw [weight_incoming ht]
  apply sum_congr rfl
  intro a _
  rw [certified_label]

theorem certified_construction {t n m : ℕ} {ht : 0 < t}
    (c : FiniteCertificate t n m ht) :
    ∃ f : Labeling (tree t n),
      (∀ (u v : Vertex t n) (h : Child u v),
        (f ⟨s(u, v), (tree t n).mem_edgeSet.mpr (Or.inl h)⟩).val + 1 =
          label t n v.1.val v.2.val) ∧
      IsLocal (tree t n) f ∧ colorCount (tree t n) f = t ^ n + 1 := by
  refine ⟨certifiedLabeling c, ?_, ?_, ?_⟩
  · intro u v h
    let a : Nonroot t n := ⟨v, by have := h.1; unfold depth; omega⟩
    have he : (⟨s(u, v), (tree t n).mem_edgeSet.mpr (Or.inl h)⟩ : (tree t n).edgeSet) = incomingEdge ht a := by
      apply Subtype.ext
      change s(u, v) = s(parent ht a, v)
      rw [← child_parent_unique h ht]
    rw [he]
    exact certified_label c a
  · intro u v h
    rw [certified_weight, certified_weight]
    exact c.proper u v h
  · unfold colorCount
    rw [show weight (tree t n) (certifiedLabeling c) = formulaWeight t n ht from
      funext (certified_weight c)]
    exact c.colors

end Antimagic
