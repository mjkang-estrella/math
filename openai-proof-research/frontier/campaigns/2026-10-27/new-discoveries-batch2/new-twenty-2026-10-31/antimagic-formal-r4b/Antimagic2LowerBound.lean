import Antimagic2Leaves
import AntimagicFinal
namespace Antimagic
open Finset

theorem weight_bottom {t n : ℕ} (ht : 0 < t) (hn : 0 < n)
    (f : Labeling (tree t n)) (v : Vertex t n) (hv : depth v = n) :
    weight (tree t n) f v = (f (incomingEdge ht ⟨v, by omega⟩)).val + 1 := by
  rw [weight_incoming ht]
  let a : Nonroot t n := ⟨v, by omega⟩
  rw [sum_eq_single a]
  · have he : v = a.val := rfl
    simp only [he, or_true, ite_true]
  · intro b _ hb
    have hne : v ≠ b.val := by
      intro he
      apply hb
      exact Subtype.ext he.symm
    have hnp : v ≠ parent ht b := by
      intro he
      have h := (parent_child ht b).1
      have hl := b.val.1.isLt
      have hh : v.1.val = n := hv
      have he' := congrArg (fun x : Vertex t n => x.1.val) he
      omega
    simp only [hne, hnp, or_self, ite_false]
  · simp

theorem weight_two_edges {t n : ℕ} (f : Labeling (tree t n))
    (v : Vertex t n) (a b : (tree t n).edgeSet) (hne : a ≠ b)
    (ha : v ∈ a.val) (hb : v ∈ b.val) :
    (f a).val + 1 + ((f b).val + 1) ≤ weight (tree t n) f v := by
  unfold weight
  have hs : {a, b} ⊆ (univ : Finset (tree t n).edgeSet) := subset_univ _
  have h := sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.zero_le _)
    (f := fun e : (tree t n).edgeSet => if v ∈ e.val then (f e).val + 1 else 0)
  simpa only [sum_pair hne, ite_eq_left ha, ite_eq_left hb] using h

theorem lowerBound : LowerBound := by
  intro t n ht hn f _hf
  have ht' : 0 < t := by omega
  have hn' : 0 < n := by omega
  let leaf : Fin (t ^ n) → Vertex t n := fun i => (bottomEquiv t n i).val
  let le : Fin (t ^ n) → (tree t n).edgeSet := fun i =>
    incomingEdge ht' ⟨leaf i, by change 0 < depth (bottomEquiv t n i).val; rw [(bottomEquiv t n i).property]; omega⟩
  have hw (i : Fin (t ^ n)) : weight (tree t n) f (leaf i) = (f (le i)).val + 1 :=
    weight_bottom ht' hn' f _ (bottomEquiv t n i).property
  have inj : Function.Injective (fun i => weight (tree t n) f (leaf i)) := by
    intro i j hij
    change weight (tree t n) f (leaf i) = weight (tree t n) f (leaf j) at hij
    rw [hw, hw] at hij
    have hfin : f (le i) = f (le j) := Fin.ext (by omega)
    have he := incomingEdge_injective ht' (f.injective hfin)
    have hv := congrArg (fun a : Nonroot t n => a.val) he
    exact (bottomEquiv t n).injective (Subtype.ext hv)
  let m := Fintype.card (tree t n).edgeSet
  have small : ∀ i, weight (tree t n) f (leaf i) ≤ m := by
    intro i
    rw [hw]
    exact (f (le i)).isLt
  have hm : 0 < m := by
    have hpow : 0 < t ^ n := pow_pos ht' n
    let i : Fin (t ^ n) := ⟨0, hpow⟩
    exact Nat.zero_lt_of_lt (f (le i)).isLt
  let e := f.symm ⟨m - 1, by omega⟩
  obtain ⟨a, hae⟩ := incomingEdge_surjective ht' e
  let u := parent ht' a
  have hu' : depth u < n := by
    have h := (parent_child ht' a).1
    have := a.val.1.isLt
    change u.1.val < n
    change a.val.1.val = u.1.val + 1 at h
    omega
  have heval : (f e).val + 1 = m := by
    change (f (f.symm ⟨m - 1, by omega⟩)).val + 1 = m
    rw [f.apply_symm_apply]
    simp only
    omega
  let b₀ := incomingEdge ht' ⟨childAt u hu' ⟨0, ht'⟩, by
    have := (childAt_child ht' u hu' ⟨0, ht'⟩).1; unfold depth; omega⟩
  let b₁ := incomingEdge ht' ⟨childAt u hu' ⟨1, ht⟩, by
    have := (childAt_child ht' u hu' ⟨1, ht⟩).1; unfold depth; omega⟩
  have hbne : b₀ ≠ b₁ := by
    intro h
    have he := incomingEdge_injective ht' h
    have hval := congrArg (fun a : Nonroot t n => a.val.2.val) he
    change t * u.2.val + 0 = t * u.2.val + 1 at hval
    omega
  have hmem (j : Fin t) : u ∈ (incomingEdge ht'
      ⟨childAt u hu' j, by have := (childAt_child ht' u hu' j).1; unfold depth; omega⟩).val := by
    have hp := child_parent_unique (childAt_child ht' u hu' j) ht'
    change u ∈ s(parent ht' _, childAt u hu' j)
    rw [← hp]
    exact Sym2.mem_mk_left _ _
  have he_mem : u ∈ e.val := by
    rw [← hae]
    exact Sym2.mem_mk_left _ _
  have large : ∃ v, m < weight (tree t n) f v := by
    refine ⟨u, ?_⟩
    by_cases h : e = b₀
    · have hle := weight_two_edges f u e b₁ (by intro he; exact hbne (h.symm.trans he)) he_mem (hmem ⟨1, ht⟩)
      rw [heval] at hle
      omega
    · have hle := weight_two_edges f u e b₀ h he_mem (hmem ⟨0, ht'⟩)
      rw [heval] at hle
      omega
  have h := leaf_color_bound (weight (tree t n) f) leaf m inj small large
  simpa only [Fintype.card_fin, colorCount] using h

#print axioms lowerBound
end Antimagic
