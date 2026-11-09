import PDTAR.ReductionMetric
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
namespace PDTAR
set_option linter.unusedSectionVars false
open Finset
open scoped symmDiff
variable {V : Type} [Fintype V] [DecidableEq V]

/-- A monotone path between nested feasible sets, with exactly the required length. -/
theorem reduction_up_walk (G : SimpleGraph V) (S T : Finset V)
    (hs : IsPD G S) (hst : S ⊆ T) :
    ∃ p : (tar G).Walk ⟨S,hs⟩ ⟨T,isPD_mono G hst hs⟩,
      p.length = (T \ S).card := by
  generalize hn : (T \ S).card = n
  induction n using Nat.strong_induction_on generalizing S with
  | h n ih =>
    by_cases he : S = T
    · subst T
      exact ⟨.nil,by simpa using hn⟩
    have hne : (T \ S).Nonempty := by
      apply nonempty_iff_ne_empty.mpr
      intro hh
      exact he (subset_antisymm hst (sdiff_eq_empty_iff_subset.mp hh))
    obtain ⟨v,hv⟩ := hne
    have hvT := (mem_sdiff.mp hv).1
    have hvS := (mem_sdiff.mp hv).2
    have hi : insert v S ⊆ T := insert_subset hvT hst
    have hp := isPD_mono G (subset_insert v S) hs
    have hd : T \ insert v S = (T \ S).erase v := by
      ext x; simp only [mem_sdiff,mem_insert,mem_erase]; tauto
    have hlt : (T \ insert v S).card < n := by
      rw [hd,card_erase_of_mem hv]
      have hpos : 0 < (T \ S).card := card_pos.mpr ⟨v,hv⟩
      omega
    obtain ⟨p,hp'⟩ := ih _ hlt (insert v S) hp hi rfl
    have ha : (tar G).Adj ⟨S,hs⟩ ⟨insert v S,hp⟩ := by
      change (S ∆ insert v S).card = 1
      have hd : S ∆ insert v S = {v} := by
        ext x; simp only [mem_symmDiff,mem_insert,mem_singleton]; aesop
      rw [hd]; simp
    refine ⟨.cons ha p,?_⟩
    simp only [SimpleGraph.Walk.length_cons, hp',hd,card_erase_of_mem hv]
    have hpos : 0 < (T \ S).card := card_pos.mpr ⟨v,hv⟩
    omega

/-- Any two feasible sets are joined by a walk of Hamming length. -/
theorem reduction_hamming_walk (G : SimpleGraph V)
    (S T : {S : Finset V // IsPD G S}) :
    ∃ p : (tar G).Walk S T, p.length = (S.val ∆ T.val).card := by
  obtain ⟨p,hp⟩ := reduction_up_walk G S.val (S.val ∪ T.val) S.property subset_union_left
  obtain ⟨q,hq⟩ := reduction_up_walk G T.val (S.val ∪ T.val) T.property subset_union_right
  refine ⟨p.append q.reverse,?_⟩
  rw [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_reverse,hp,hq]
  have h₁ : (S.val ∪ T.val) \ S.val = T.val \ S.val := by ext x; simp; tauto
  have h₂ : (S.val ∪ T.val) \ T.val = S.val \ T.val := by ext x; simp; tauto
  rw [h₁,h₂,symmDiff_def]
  change _ = ((S.val \ T.val) ∪ (T.val \ S.val)).card
  rw [card_union_of_disjoint (by
    apply disjoint_left.mpr
    intro x hx hy
    exact (mem_sdiff.mp hx).2 (mem_sdiff.mp hy).1)]
  omega

/-- The Hamming triangle inequality, without introducing a metric instance. -/
theorem reduction_hamming_triangle (S T U : Finset V) :
    (S ∆ U).card ≤ (S ∆ T).card + (T ∆ U).card := by
  have hh : S ∆ U ⊆ (S ∆ T) ∪ (T ∆ U) := by
    intro x hx
    simp only [mem_symmDiff,mem_union] at hx ⊢
    tauto
  exact (card_le_card hh).trans (card_union_le _ _)

/-- Each walk has length at least its endpoint Hamming distance. -/
theorem reduction_walk_lower (G : SimpleGraph V)
    {S T : {S : Finset V // IsPD G S}} (p : (tar G).Walk S T) :
    (S.val ∆ T.val).card ≤ p.length := by
  induction p with
  | nil => simp
  | @cons S U T ha p ih =>
    have ht := reduction_hamming_triangle S.val U.val T.val
    have hc : (S.val ∆ U.val).card = 1 := ha
    simp only [SimpleGraph.Walk.length_cons]
    omega

/-- Discharges the metric obligation using walks in the two directions. -/
theorem reductionHammingRemaining : ReductionHammingRemaining := by
  intro V W _ _ _ _ G H φ S T
  obtain ⟨p,hp⟩ := reduction_hamming_walk G S T
  have h₁ := reduction_walk_lower H (p.map φ.toHom)
  rw [SimpleGraph.Walk.length_map,hp] at h₁
  obtain ⟨q,hq⟩ := reduction_hamming_walk H (φ S) (φ T)
  have h₂ := reduction_walk_lower G (q.map φ.symm.toHom)
  have heS : φ.symm.toHom (φ S) = S := φ.toEquiv.symm_apply_apply S
  have heT : φ.symm.toHom (φ T) = T := φ.toEquiv.symm_apply_apply T
  rw [SimpleGraph.Walk.length_map,hq] at h₂
  rw [heS,heT] at h₂
  exact Nat.le_antisymm h₁ h₂
end PDTAR
