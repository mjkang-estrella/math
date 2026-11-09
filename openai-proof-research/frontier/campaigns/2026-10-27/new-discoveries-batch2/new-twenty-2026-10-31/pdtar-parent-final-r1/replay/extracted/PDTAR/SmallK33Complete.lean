import PDTAR.SmallK33Degree
namespace PDTAR
open Finset
attribute [local instance] Classical.propDecidable

/-- A balanced complete partition supplies the required graph isomorphism. -/
theorem small_k33_iso {H : SimpleGraph (Fin 3 ⊕ Fin 3)}
    (A : Finset (Fin 3 ⊕ Fin 3)) (ha : A.card = 3)
    (hb : (univ \ A).card = 3)
    (hadj : ∀ x y, H.Adj x y ↔ (x ∈ A ∧ y ∉ A) ∨ (x ∉ A ∧ y ∈ A)) :
    Nonempty (H ≃g completeBipartiteGraph (Fin 3) (Fin 3)) := by
  classical
  let eA : Fin 3 ≃ {x // x ∈ A} := (Fintype.equivFinOfCardEq (by simpa using ha)).symm
  let eB : Fin 3 ≃ {x // x ∉ A} := (Fintype.equivFinOfCardEq (by
    have hh : Fintype.card {x // x ∉ A} = (univ \ A).card := by simp [card_sdiff]
    omega)).symm
  let e := (Equiv.sumCongr eA eB).trans (Equiv.sumCompl (fun x => x ∈ A))
  have hi : completeBipartiteGraph (Fin 3) (Fin 3) ≃g H :=
    { toEquiv := e
      map_rel_iff' := by
        intro x y
        cases x with
        | inl x =>
          cases y with
          | inl y =>
            change H.Adj (eA x).val (eA y).val ↔ _
            simp [hadj,(eA x).property,(eA y).property,completeBipartiteGraph]
          | inr y =>
            change H.Adj (eA x).val (eB y).val ↔ _
            simp [hadj,(eA x).property,(eB y).property,completeBipartiteGraph]
        | inr x =>
          cases y with
          | inl y =>
            change H.Adj (eB x).val (eA y).val ↔ _
            simp [hadj,(eB x).property,(eA y).property,completeBipartiteGraph]
          | inr y =>
            change H.Adj (eB x).val (eB y).val ↔ _
            simp [hadj,(eB x).property,(eB y).property,completeBipartiteGraph] }
  exact ⟨hi.symm⟩

theorem threeThreeRigidityRemaining : ThreeThreeRigidityRemaining := by
  intro H hH he
  classical
  let v : Fin 3 ⊕ Fin 3 := Sum.inl 0
  let N := univ.filter (H.Adj v)
  have hN : N.card = 3 := small_k33_degree hH he v
  have hvN : v ∉ N := by simp [N]
  have hclosed : closed H {v} = insert v N := by ext u; simp [N,mem_closed,H.adj_comm]
  have hsize : (univ : Finset (Fin 3 ⊕ Fin 3)).card = 6 := by simp
  have hnot : ¬ IsPD H {v} := fun h => small_k33_singleton v ((he _).mpr h)
  have hd := (fort_duality H {v}).not.mp hnot
  push Not at hd
  obtain ⟨F,hf,havoid⟩ := hd
  have hsub : F ⊆ univ \ closed H {v} := by
    intro x hx
    refine mem_sdiff.mpr ⟨mem_univ _,?_⟩
    intro hc
    have hh := mem_inter.mpr ⟨hx,hc⟩
    rw [havoid] at hh; simp at hh
  have hFc : F.card = 2 := by
    have hu := card_sdiff_of_subset (subset_univ (closed H {v}))
    have hc : (closed H {v}).card = 4 := by rw [hclosed,card_insert_of_notMem hvN,hN]
    have hle := card_le_card hsub
    have hlo : 2 ≤ F.card := by
      by_contra! hn
      have hone : F.card = 1 := by have := hf.1.card_pos; omega
      obtain ⟨x,hx⟩ := card_eq_one.mp hone
      obtain ⟨y,hy⟩ := hH x
      exact (singleton_fort_iff H x).mp (hx ▸ hf) y hy
    omega
  have hFeq : F = univ \ closed H {v} := by
    apply eq_of_subset_of_card_le hsub
    rw [card_sdiff_of_subset (subset_univ _),hclosed,card_insert_of_notMem hvN,hN,hsize,hFc]
  have hvC : v ∉ closed H F := by
    intro hv
    obtain ⟨w,hw⟩ := (closed_inter_comm H F {v}).mpr ⟨v,by simp [hv]⟩
    rw [havoid] at hw; simp at hw
  have hC : closed H F = univ.erase v := by
    ext u
    constructor
    · intro hu
      exact mem_erase.mpr ⟨fun huv => hvC (huv ▸ hu),mem_univ _⟩
    · intro hu
      have huv := (mem_erase.mp hu).1
      have hp := (he _).mp (small_k33_pair v u huv.symm)
      obtain ⟨w,hw⟩ := (closed_inter_comm H F {v,u}).mp ((fort_duality H _).mp hp F hf)
      rcases mem_insert.mp (mem_inter.mp hw).2 with hwv | hwu
      · exact False.elim (hvC (hwv ▸ (mem_inter.mp hw).1))
      · exact mem_singleton.mp hwu ▸ (mem_inter.mp hw).1
  obtain ⟨x,y,hxy,hF⟩ := card_eq_two.mp hFc
  have hvF : v ∉ F := fun h => hvC (subset_closed H F h)
  let A := insert v F
  let B := univ \ A
  have hA : A.card = 3 := by simp [A,card_insert_of_notMem hvF,hFc]
  have hB : B.card = 3 := by dsimp [B]; rw [card_sdiff_of_subset (subset_univ _),hsize,hA]
  have hcross : ∀ a ∈ A, ∀ b ∈ B, H.Adj a b := by
    intro a ha b hb
    have hbA := (mem_sdiff.mp hb).2
    have hbv : b ≠ v := fun h => hbA (by simp [A,h])
    have hbF : b ∉ F := fun h => hbA (mem_insert_of_mem h)
    rcases mem_insert.mp ha with rfl | haF
    · have hbcl : b ∈ closed H {v} := by
        by_contra hn
        exact hbF (hFeq ▸ (by simp [hn]))
      rcases (mem_closed H _ _).mp hbcl with hb | ⟨u,hu,hub⟩
      · exact False.elim (hbv (mem_singleton.mp hb))
      · exact mem_singleton.mp hu ▸ hub
    · have hbC : b ∈ closed H F := by rw [hC]; simp [hbv]
      obtain ⟨u,hu,w,hw,huw,hbu,hbw⟩ := fort_two_neighbors H hf hbC hbF
      rw [hF] at hu hw haF
      rcases core_pair_exhaust (by simpa using hu) (by simpa using hw) huw with h | h
      · rcases mem_insert.mp haF with hax | hay
        · exact hax ▸ h.1 ▸ hbu.symm
        · exact mem_singleton.mp hay ▸ h.2 ▸ hbw.symm
      · rcases mem_insert.mp haF with hax | hay
        · exact hax ▸ h.2 ▸ hbw.symm
        · exact mem_singleton.mp hay ▸ h.1 ▸ hbu.symm
  have hsat : ∀ a ∈ A, univ.filter (H.Adj a) = B := by
    intro a ha
    apply eq_of_subset_of_card_le
    · intro b hb
      -- Equal cardinality converts the cross-edge inclusion to equality.
      have hs : B ⊆ univ.filter (H.Adj a) := by intro b hb; simp [hcross a ha b hb]
      have heq : B = univ.filter (H.Adj a) := eq_of_subset_of_card_le hs (by
        rw [hB,small_k33_degree hH he a])
      exact heq ▸ hb
    · rw [hB,small_k33_degree hH he a]
  have hsatB : ∀ b ∈ B, univ.filter (H.Adj b) = A := by
    intro b hb
    have hs : A ⊆ univ.filter (H.Adj b) := by intro a ha; simp [(hcross a ha b hb).symm]
    exact (eq_of_subset_of_card_le hs (by rw [hA,small_k33_degree hH he b])).symm
  apply small_k33_iso A hA hB
  intro a b
  by_cases ha : a ∈ A
  · rw [show H.Adj a b ↔ b ∈ B by
      have hh := congrArg (fun S => b ∈ S) (hsat a ha)
      simpa using hh]
    simp [B,ha]
  · have haB : a ∈ B := by simp [B,ha]
    rw [show H.Adj a b ↔ b ∈ A by
      have hh := congrArg (fun S => b ∈ S) (hsatB a haB)
      simpa using hh]
    simp [ha]
#print axioms threeThreeRigidityRemaining
end PDTAR
