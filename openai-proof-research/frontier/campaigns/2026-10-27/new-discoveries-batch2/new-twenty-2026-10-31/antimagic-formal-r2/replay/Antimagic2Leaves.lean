import Antimagic2Structure
namespace Antimagic
open Finset

theorem parent_count {t n : ℕ} (ht : 0 < t) (v : Vertex t n) :
    (univ.filter fun u => Child u v).card = if depth v = 0 then 0 else 1 := by
  split_ifs with hv
  · have he : (univ.filter fun u => Child u v) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro u hu
      have := (mem_filter.mp hu).2.1
      unfold depth at hv
      omega
    rw [he, card_empty]
  · let a : Nonroot t n := ⟨v, by omega⟩
    have he : (univ.filter fun u => Child u v) = {parent ht a} := by
      ext u
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      exact ⟨fun h => child_parent_unique h ht, fun h => h ▸ parent_child ht a⟩
    rw [he, card_singleton]

theorem degree_formula {t n : ℕ} (ht : 0 < t) (v : Vertex t n) :
    (tree t n).degree v = (if depth v < n then t else 0) +
      (if depth v = 0 then 0 else 1) := by
  have he : (tree t n).neighborFinset v =
      (univ.filter (Child v)) ∪ (univ.filter fun u => Child u v) := by
    ext u
    simp only [SimpleGraph.mem_neighborFinset, mem_union, mem_filter, mem_univ, true_and]
    rfl
  have hd : Disjoint (univ.filter (Child v)) (univ.filter fun u => Child u v) := by
    apply disjoint_left.mpr
    intro u hu hv
    have h₁ := (mem_filter.mp hu).2.1
    have h₂ := (mem_filter.mp hv).2.1
    omega
  rw [← SimpleGraph.card_neighborFinset_eq_degree, he, card_union_of_disjoint hd,
    children_count ht, parent_count ht]

theorem degree_one_iff {t n : ℕ} (ht : 2 ≤ t) (hn : 1 ≤ n) (v : Vertex t n) :
    (tree t n).degree v = 1 ↔ depth v = n := by
  rw [degree_formula (by omega)]
  have := v.1.isLt
  unfold depth
  split_ifs <;> omega

def bottomEquiv (t n : ℕ) : Fin (t ^ n) ≃ {v : Vertex t n // depth v = n} where
  toFun i := ⟨⟨⟨n, by omega⟩, i⟩, rfl⟩
  invFun v := ⟨v.val.2.val, by have h := v.val.2.isLt; change v.val.2.val < t ^ depth v.val at h; exact h.trans_le (le_of_eq (congrArg (fun k => t ^ k) v.property))⟩
  left_inv _ := rfl
  right_inv v := by
    apply Subtype.ext
    apply Sigma.ext
    · apply Fin.ext; exact v.property.symm
    · apply (Fin.heq_ext_iff (by congr 1; exact v.property.symm)).mpr
      rfl

theorem modelLeaves : ModelLeaves := by
  intro t n ht hn
  unfold numLeaves
  simp only [degree_one_iff ht hn]
  rw [← Fintype.card_subtype, ← Fintype.card_congr (bottomEquiv t n)]
  exact Fintype.card_fin _

#print axioms modelLeaves
end Antimagic
