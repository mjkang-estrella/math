import PDTAR.CoreProofLocal
namespace PDTAR
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]

/-- F1 restricted to the side on which a pair fort is supported. -/
theorem core_pair_internal {H : SimpleGraph V} {A B F : Finset V}
    (hp : Parts A B) {x y u v : V} (hc : closed H F = B ∪ {x,y})
    (hu : u ∈ F) (hv : v ∈ A) (ha : H.Adj u v) : v = x ∨ v = y := by
  have h := core_fort_neighbor hu ha
  rw [hc] at h
  rcases mem_union.mp h with h | h
  · exact False.elim (hp.not_both hv h)
  · simpa only [mem_insert,mem_singleton] using h

/-- Lemma 5(i): a vertex with exactly one cross neighbour is an internal hub;
its cross neighbour sees no other vertex on this side, and other internal
vertices see only the hub. This statement is uniform in the ordered parts. -/
theorem core_hub_step_i {K H : SimpleGraph V} {A B : Finset V}
    (hk : CompleteBetween K A B) (he : SamePD K H)
    (ha : 3 ≤ A.card) (hb : 3 ≤ B.card) {a c : V}
    (haA : a ∈ A) (hcB : c ∈ B)
    (hcross : ∀ b ∈ B, H.Adj a b ↔ b = c) :
    (∀ y ∈ A, y ≠ a → H.Adj a y) ∧
    (∀ y ∈ A, H.Adj c y ↔ y = a) ∧
    (∀ y ∈ A, y ≠ a → ∀ z ∈ A, H.Adj y z ↔ z = a) := by
  classical
  have hac : H.Adj a c := (hcross c hcB).mpr rfl
  have hinside : ∃ z ∈ A, H.Adj a z := by
    by_contra! hn
    apply core_no_cross_leaf hk he (by omega) hb haA hcB
    refine ⟨hac,fun u hu => ?_⟩
    rcases hk.1.mem_or u with huA | huB
    · exact False.elim (hn u huA hu)
    · exact (hcross u huB).mp hu
  have hrestrict : ∀ y ∈ A, y ≠ a → ∀ F, IsFort H F →
      closed H F = B ∪ {a,y} → ∀ u ∈ F, H.Adj a u → u = c ∨ u = y := by
    intro y _ _ F _ hC u hu hau
    have huC := subset_closed H F hu
    rw [hC] at huC
    rcases mem_union.mp huC with huB | hup
    · exact .inl ((hcross u huB).mp hau)
    · rcases mem_insert.mp hup with hua | huy
      · exact False.elim (H.ne_of_adj hau hua.symm)
      · exact .inr (mem_singleton.mp huy)
  have hall : ∀ y ∈ A, y ≠ a → H.Adj a y := by
    intro y hy hya
    obtain ⟨F,hf,hC⟩ := pair_fort hk he ha (by omega) haA hy hya.symm
    by_contra hnon
    have haC : a ∈ closed H F := by rw [hC]; simp
    have haF : a ∈ F := by
      by_contra hn
      obtain ⟨u,hu,w,hw,huw,hau,haw⟩ := fort_two_neighbors H hf haC hn
      have huC : u = c := (hrestrict y hy hya F hf hC u hu hau).resolve_right
        (fun huy => hnon (huy ▸ hau))
      have hwC : w = c := (hrestrict y hy hya F hf hC w hw haw).resolve_right
        (fun hwy => hnon (hwy ▸ haw))
      exact huw (huC.trans hwC.symm)
    obtain ⟨z,hz,haz⟩ := hinside
    have hzY : z = y := (core_pair_internal hk.1 hC haF hz haz).resolve_left
      (fun hza => H.ne_of_adj haz hza.symm)
    exact hnon (hzY ▸ haz)
  have hfort : ∀ y ∈ A, y ≠ a → ∃ F, IsFort H F ∧
      closed H F = B ∪ {a,y} ∧ c ∈ F ∧ y ∈ F := by
    intro y hy hya
    obtain ⟨F,hf,hC⟩ := pair_fort hk he ha (by omega) haA hy hya.symm
    have haC : a ∈ closed H F := by rw [hC]; simp
    have haF : a ∉ F := by
      intro haF
      obtain ⟨z,hz,hza,hzy⟩ := core_third ha a y
      exact (core_pair_internal hk.1 hC haF hz (hall z hz hza)).elim hza hzy
    obtain ⟨u,hu,w,hw,huw,hau,haw⟩ := fort_two_neighbors H hf haC haF
    have hu2 := hrestrict y hy hya F hf hC u hu hau
    have hw2 := hrestrict y hy hya F hf hC w hw haw
    have hcF : c ∈ F := by
      rcases hu2 with rfl | rfl
      · exact hu
      · rcases hw2 with rfl | rfl
        · exact hw
        · exact False.elim (huw rfl)
    have hyF : y ∈ F := by
      rcases hw2 with rfl | rfl
      · rcases hu2 with rfl | rfl
        · exact False.elim (huw rfl)
        · exact hu
      · exact hw
    exact ⟨F,hf,hC,hcF,hyF⟩
  refine ⟨hall,?_,?_⟩
  · intro z hz
    constructor
    · intro hcz
      by_contra hza
      obtain ⟨y,hy,hya,hyz⟩ := core_third ha a z
      obtain ⟨F,_,hC,hcF,_⟩ := hfort y hy hya
      exact (core_pair_internal hk.1 hC hcF hz hcz).elim hza (Ne.symm hyz)
    · rintro rfl; exact hac.symm
  · intro y hy hya z hz
    constructor
    · intro hyz
      obtain ⟨F,_,hC,_,hyF⟩ := hfort y hy hya
      exact (core_pair_internal hk.1 hC hyF hz hyz).resolve_right
        (fun hzy => H.ne_of_adj hyz hzy.symm)
    · rintro rfl; exact (hall y hy hya).symm
end PDTAR
