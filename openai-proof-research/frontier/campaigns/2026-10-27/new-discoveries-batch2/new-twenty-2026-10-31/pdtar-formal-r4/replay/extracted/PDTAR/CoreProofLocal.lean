import PDTAR.Remaining
namespace PDTAR
set_option linter.unusedSectionVars false
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Lemma 1(b), with only the size assumptions used by K1. -/
theorem core_noIsolated {K H : SimpleGraph V} {A B : Finset V}
    (hk : CompleteBetween K A B) (he : SamePD K H)
    (ha : 2 ≤ A.card) (hb : 2 ≤ B.card) : NoIsolated H := by
  classical
  intro v
  by_contra! hn
  have hf := (singleton_fort_iff H v).mpr hn
  have hc : closed H {v} = {v} := by
    ext u
    simp only [mem_closed, mem_singleton]
    constructor
    · rintro (h | ⟨w,hw,hadj⟩)
      · exact h
      · exact False.elim (hn u (hw ▸ hadj))
    · exact Or.inl
  rcases fort_covers_side hk he hf with h | h
  · rw [hc] at h
    have := card_le_card h
    simp only [card_singleton] at this
    omega
  · rw [hc] at h
    have := card_le_card h
    simp only [card_singleton] at this
    omega

/-- A finite part of size at least three contains a vertex outside two prescribed vertices. -/
theorem core_third {A : Finset V} (ha : 3 ≤ A.card) (x y : V) :
    ∃ z ∈ A, z ≠ x ∧ z ≠ y := by
  classical
  by_contra! h
  have hs : A ⊆ {x,y} := by
    intro z hz
    simp only [mem_insert, mem_singleton]
    by_cases he : z = x
    · exact .inl he
    · exact .inr (h z hz he)
  have hc := card_le_card hs
  have ht : ({x,y} : Finset V).card ≤ 2 := by
    by_cases hxy : x = y <;> simp [hxy]
  omega

/-- Membership in a fort controls every neighbour through its closed neighbourhood. -/
theorem core_fort_neighbor {H : SimpleGraph V} {F : Finset V} {u v : V}
    (hu : u ∈ F) (hadj : H.Adj u v) : v ∈ closed H F :=
  (mem_closed H F v).mpr (.inr ⟨u,hu,hadj⟩)

/-- Lemma 3: each vertex has a neighbour across the ordered partition. -/
theorem core_cross_nonempty {K H : SimpleGraph V} {A B : Finset V}
    (hk : CompleteBetween K A B) (he : SamePD K H)
    (ha : 3 ≤ A.card) (hb : 2 ≤ B.card) {p : V} (hp : p ∈ A) :
    ∃ b ∈ B, H.Adj p b := by
  classical
  by_contra! hn
  have hside : ∀ u, H.Adj p u → u ∈ A := by
    intro u hu
    exact (hk.1.mem_or u).resolve_right (fun hb => hn u hb hu)
  have hybound : ∀ y ∈ A, y ≠ p → ∀ u, H.Adj p u → u = y := by
    intro y hy hyp
    obtain ⟨F,hf,hc⟩ := pair_fort hk he ha hb hp hy hyp.symm
    have hsub : ∀ u ∈ F, u ∈ B ∨ u = p ∨ u = y := by
      intro u hu
      have hh := subset_closed H F hu
      rw [hc] at hh
      simpa only [mem_union, mem_insert, mem_singleton] using hh
    have hpC : p ∈ closed H F := by rw [hc]; simp
    have hpF : p ∈ F := by
      by_contra hpF
      obtain ⟨u,hu,w,hw,hne,hpu,hpw⟩ := fort_two_neighbors H hf hpC hpF
      have huY : u = y := by
        rcases hsub u hu with hu | hu | hu
        · exact False.elim (hn u hu hpu)
        · exact False.elim (H.ne_of_adj hpu hu.symm)
        · exact hu
      have hwY : w = y := by
        rcases hsub w hw with hw | hw | hw
        · exact False.elim (hn w hw hpw)
        · exact False.elim (H.ne_of_adj hpw hw.symm)
        · exact hw
      exact hne (huY.trans hwY.symm)
    intro u hpu
    have hu := core_fort_neighbor hpF hpu
    rw [hc] at hu
    rcases mem_union.mp hu with hu | hu
    · exact False.elim (hn u hu hpu)
    · rcases mem_insert.mp hu with hu | hu
      · exact False.elim (H.ne_of_adj hpu hu.symm)
      · exact mem_singleton.mp hu
  obtain ⟨u,hpu⟩ := core_noIsolated hk he (by omega) hb p
  obtain ⟨y,hy,hyp,hyu⟩ := core_third ha p u
  exact hyu (hybound y hy hyp u hpu).symm

/-- Lemma 4: a leaf cannot have its sole neighbour across the partition. -/
theorem core_no_cross_leaf {K H : SimpleGraph V} {A B : Finset V}
    (hk : CompleteBetween K A B) (he : SamePD K H)
    (ha : 2 ≤ A.card) (hb : 3 ≤ B.card) {a c : V}
    (haA : a ∈ A) (hcB : c ∈ B) :
    ¬ (H.Adj a c ∧ ∀ u, H.Adj a u → u = c) := by
  classical
  rintro ⟨hac,hleaf⟩
  obtain ⟨x,hx,hxc,_⟩ := core_third hb c c
  obtain ⟨y,hy,hyc,hyx⟩ := core_third hb c x
  obtain ⟨F,hf,hC⟩ := pair_fort (completeBetween_swap hk) he hb ha hx hy hyx.symm
  have haC : a ∈ closed H F := by rw [hC]; simp [haA]
  have haF : a ∈ F := by
    by_contra hn
    obtain ⟨u,_,w,_,huw,hu,hw⟩ := fort_two_neighbors H hf haC hn
    exact huw ((hleaf u hu).trans (hleaf w hw).symm)
  have hcC := core_fort_neighbor haF hac
  rw [hC] at hcC
  rcases mem_union.mp hcC with hcA | hcp
  · exact hk.1.not_both hcA hcB
  · simp only [mem_insert, mem_singleton] at hcp
    exact hcp.elim (fun h => hxc h.symm) (fun h => hyc h.symm)
end PDTAR
