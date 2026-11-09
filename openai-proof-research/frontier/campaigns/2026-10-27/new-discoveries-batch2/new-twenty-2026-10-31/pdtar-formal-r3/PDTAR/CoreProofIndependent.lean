import PDTAR.CoreProofLocal
namespace PDTAR
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]

/-- In a graph with no isolated vertices, a fort contained in a pair is the whole pair. -/
theorem core_pair_fort_eq {H : SimpleGraph V} (hH : NoIsolated H)
    {F : Finset V} (hf : IsFort H F) {x y : V} (hs : F ⊆ {x,y}) : F = {x,y} := by
  classical
  have hn : ∀ z, F ≠ {z} := by
    intro z heq
    obtain ⟨w,hw⟩ := hH z
    exact ((singleton_fort_iff H z).mp (heq ▸ hf)) w hw
  have hc : 2 ≤ F.card := by
    by_contra! hc
    have hc1 : F.card = 1 := by have := hf.1.card_pos; omega
    obtain ⟨z,hz⟩ := card_eq_one.mp hc1
    exact hn z hz
  apply eq_of_subset_of_card_le hs
  have hp : ({x,y} : Finset V).card ≤ 2 := by
    by_cases hxy : x = y <;> simp [hxy]
  omega

/-- Lemma 7, one ordered side; the mirror is obtained by exchanging A and B. -/
theorem core_side_independent {K H : SimpleGraph V} {A B : Finset V}
    (hk : CompleteBetween K A B) (he : SamePD K H)
    (ha : 3 ≤ A.card) (hb : 2 ≤ B.card)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, H.Adj a b) :
    ∀ x ∈ A, ∀ z ∈ A, ¬ H.Adj x z := by
  classical
  intro x hx z hz hxz
  obtain ⟨y,hy,hyx,hyz⟩ := core_third ha x z
  obtain ⟨F,hf,hC⟩ := pair_fort hk he ha hb hx hy hyx.symm
  have hzC : z ∉ closed H F := by
    rw [hC]
    simp only [mem_union, mem_insert, mem_singleton, not_or]
    exact ⟨fun h => hk.1.not_both hz h, H.ne_of_adj hxz |>.symm, hyz.symm⟩
  have hsub : F ⊆ {x,y} := by
    intro u hu
    have huC := subset_closed H F hu
    rw [hC] at huC
    rcases mem_union.mp huC with huB | hup
    · exact False.elim (hzC (core_fort_neighbor hu (hcross z hz u huB).symm))
    · exact hup
  have hF := core_pair_fort_eq (core_noIsolated hk he (by omega) hb) hf hsub
  have hxF : x ∈ F := by rw [hF]; simp
  exact hzC (core_fort_neighbor hxF hxz)

/-- Core equality after the cross-completeness step, using the independently proved Lemma 7. -/
theorem core_eq_of_cross_complete {K H : SimpleGraph V} {A B : Finset V}
    (hk : CompleteBetween K A B) (he : SamePD K H)
    (ha : 3 ≤ A.card) (hb : 3 ≤ B.card)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, H.Adj a b) : H = K := by
  have hA := core_side_independent hk he ha (by omega) hcross
  have hB := core_side_independent (completeBetween_swap hk) he hb (by omega)
    (fun b hb a ha => (hcross a ha b hb).symm)
  ext x y
  rw [hk.2]
  constructor
  · intro hxy
    rcases hk.1.mem_or x with hx | hx <;> rcases hk.1.mem_or y with hy | hy
    · exact False.elim (hA x hx y hy hxy)
    · exact .inl ⟨hx,hy⟩
    · exact .inr ⟨hx,hy⟩
    · exact False.elim (hB x hx y hy hxy)
  · rintro (⟨hx,hy⟩ | ⟨hx,hy⟩)
    · exact hcross x hx y hy
    · exact (hcross y hy x hx).symm
end PDTAR
