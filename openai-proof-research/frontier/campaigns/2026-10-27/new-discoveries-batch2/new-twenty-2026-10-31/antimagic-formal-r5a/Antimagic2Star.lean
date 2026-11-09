import Antimagic2Incidence
import Mathlib.Algebra.BigOperators.Fin
namespace Antimagic
open Finset

def starEquiv (t : ℕ) : Nonroot t 1 ≃ Fin t where
  toFun v := ⟨v.val.2.val, by
    have hh : v.val.1.val = 1 := by have := v.val.1.isLt; have := v.property; unfold depth at this; omega
    have h := v.val.2.isLt
    exact h.trans_le (le_of_eq (by rw [hh, pow_one]))⟩
  invFun i := ⟨⟨⟨1, by omega⟩, ⟨i.val, by simpa only [pow_one] using i.isLt⟩⟩, by change 0 < 1; omega⟩
  left_inv v := by
    apply Subtype.ext
    apply Sigma.ext
    · apply Fin.ext
      change 1 = v.val.1.val
      have := v.val.1.isLt; have := v.property; unfold depth at this; omega
    · apply (Fin.heq_ext_iff (by
        congr 1
        change 1 = v.val.1.val
        have := v.val.1.isLt; have := v.property; unfold depth at this; omega)).mpr
      rfl
  right_inv _ := rfl

noncomputable def starLabeling (t : ℕ) (ht : 0 < t) : Labeling (tree t 1) :=
  (incomingEquiv ht).symm.trans ((starEquiv t).trans
    (finCongr (by rw [← Fintype.card_congr (incomingEquiv ht),
      Fintype.card_congr (starEquiv t), Fintype.card_fin])))

theorem star_label (t : ℕ) (ht : 0 < t) (a : Nonroot t 1) :
    (starLabeling t ht (incomingEdge ht a)).val + 1 = label t 1 a.val.1.val a.val.2.val := by
  change (starLabeling t ht ((incomingEquiv ht) a)).val + 1 = _
  simp only [starLabeling, Equiv.trans_apply, Equiv.symm_apply_apply, finCongr_apply,
    Fin.val_cast]
  rfl

theorem star_root_large (t : ℕ) (ht : 2 ≤ t) :
    t < weight (tree t 1) (starLabeling t (by omega)) (root t 1) := by
  have ht' : 0 < t := by omega
  let a := (starEquiv t).symm ⟨t - 1, by omega⟩
  let b := (starEquiv t).symm ⟨0, ht'⟩
  have hp (c : Nonroot t 1) : parent ht' c = root t 1 := by
    apply unique_depth_zero
    change c.val.1.val - 1 = 0
    have := c.val.1.isLt
    omega
  have hne : incomingEdge ht' a ≠ incomingEdge ht' b := by
    intro h
    have he := congrArg (fun c => ((starEquiv t) c).val) (incomingEdge_injective ht' h)
    change ((starEquiv t) ((starEquiv t).symm _)).val =
      ((starEquiv t) ((starEquiv t).symm _)).val at he
    simp only [Equiv.apply_symm_apply] at he
    omega
  have hmem (c : Nonroot t 1) : root t 1 ∈ (incomingEdge ht' c).val := by
    change root t 1 ∈ s(parent ht' c, c.val)
    rw [hp]
    exact Sym2.mem_mk_left _ _
  have hle := weight_two_edges (starLabeling t ht') (root t 1) _ _ hne (hmem a) (hmem b)
  rw [star_label, star_label] at hle
  have ha : a.val.2.val = t - 1 := by
    have h := (starEquiv t).apply_symm_apply ⟨t - 1, by omega⟩
    exact congrArg Fin.val h
  have hb : b.val.2.val = 0 := by
    have h := (starEquiv t).apply_symm_apply ⟨0, ht'⟩
    exact congrArg Fin.val h
  simp only [label, ite_true] at hle
  rw [ha, hb] at hle
  omega

theorem star_local (t : ℕ) (ht : 2 ≤ t) :
    IsLocal (tree t 1) (starLabeling t (by omega)) := by
  have ht' : 0 < t := by omega
  have hsmall (v : Vertex t 1) (hv : depth v = 1) :
      weight (tree t 1) (starLabeling t ht') v ≤ t := by
    rw [weight_bottom ht' (by omega) _ v hv, star_label]
    simp only [label, ite_true]
    have h := v.2.isLt
    have hh : v.1.val = 1 := hv
    have hh' : t ^ v.1.val = t := by rw [hh, pow_one]
    have hbound := h.trans_le (le_of_eq hh')
    omega
  have hdir (u v : Vertex t 1) (h : Child u v) :
      weight (tree t 1) (starLabeling t ht') u ≠
        weight (tree t 1) (starLabeling t ht') v := by
    have hu := u.1.isLt
    have hv := v.1.isLt
    have hh := h.1
    have hz : depth u = 0 := by unfold depth; omega
    have ho : depth v = 1 := by unfold depth; omega
    rw [unique_depth_zero u hz]
    have := star_root_large t ht
    have := hsmall v ho
    omega
  intro u v h
  rcases h with h | h
  · exact hdir u v h
  · exact (hdir v u h).symm

theorem star_construction (t : ℕ) (ht : 2 ≤ t) :
    ∃ f : Labeling (tree t 1),
      (∀ (u v : Vertex t 1) (h : Child u v),
        (f ⟨s(u, v), (tree t 1).mem_edgeSet.mpr (Or.inl h)⟩).val + 1 =
          label t 1 v.1.val v.2.val) ∧
      IsLocal (tree t 1) f ∧ colorCount (tree t 1) f = t ^ 1 + 1 := by
  have ht' : 0 < t := by omega
  refine ⟨starLabeling t ht', ?_, star_local t ht, ?_⟩
  · intro u v h
    let a : Nonroot t 1 := ⟨v, by have := h.1; unfold depth; omega⟩
    have he : (⟨s(u, v), (tree t 1).mem_edgeSet.mpr (Or.inl h)⟩ : (tree t 1).edgeSet) = incomingEdge ht' a := by
      apply Subtype.ext
      change s(u, v) = s(parent ht' a, v)
      rw [← child_parent_unique h ht']
    rw [he]
    exact star_label t ht' a
  · apply Nat.le_antisymm
    · unfold colorCount
      have h := card_image_le (s := (univ : Finset (Vertex t 1))) (f := weight (tree t 1) (starLabeling t ht'))
      have hc : Fintype.card (Vertex t 1) = 1 + t := by
        rw [Fintype.card_sigma]
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ]; simp
      simp only [card_univ, hc, pow_one] at h ⊢
      omega
    · exact lowerBound t 1 ht (by omega) _ (star_local t ht)

#print axioms star_construction
end Antimagic
