import Normalization
set_option autoImplicit false
namespace Polyomino57

theorem grown_coordinate_bound {P : Finset GridPoint} (h : Grown P) :
    ∀ p ∈ P, ∀ q ∈ P,
      (p.1-q.1).natAbs ≤ P.card-1 ∧ (p.2-q.2).natAbs ≤ P.card-1 := by
  induction h with
  | singleton a =>
    intro p hp q hq
    have hp' := Finset.mem_singleton.mp hp
    have hq' := Finset.mem_singleton.mp hq
    subst p; subst q
    simp
  | @insert Q a b _ ha hb hab ih =>
    intro p hp q hq
    rw [Finset.card_insert_of_notMem hb]
    have hc : 1 ≤ Q.card := Finset.card_pos.mpr ⟨a,ha⟩
    have had := (adj_manhattan a b).mp hab
    rcases Finset.mem_insert.mp hp with hpB | hpOld
    · subst p
      rcases Finset.mem_insert.mp hq with hqB | hqOld
      · subst q; simp
      · have he := ih a ha q hqOld
        omega
    · rcases Finset.mem_insert.mp hq with hqB | hqOld
      · subst q
        have he := ih p hpOld a ha
        omega
      · have he := ih p hpOld q hqOld
        omega

theorem normalized_coordinate_bound {P : Finset GridPoint} (h : EdgeConnected P)
    (q : GridPoint) (hq : q ∈ normalize P h.1) :
    0 ≤ q.1 ∧ q.1 ≤ (P.card : ℤ)-1 ∧ 0 ≤ q.2 ∧ q.2 ≤ (P.card : ℤ)-1 := by
  have hn := normalize_nonnegative P h.1 q hq
  obtain ⟨p,hp,hpq⟩ := Finset.mem_image.mp hq
  have hxmem := Finset.min'_mem (P.image Prod.fst) (h.1.image _)
  obtain ⟨x,hx,hxeq⟩ := Finset.mem_image.mp hxmem
  have hymem := Finset.min'_mem (P.image Prod.snd) (h.1.image _)
  obtain ⟨y,hy,hyeq⟩ := Finset.mem_image.mp hymem
  have hbx := grown_coordinate_bound (growth_complete h) p hp x hx
  have hby := grown_coordinate_bound (growth_complete h) p hp y hy
  have hc : 1 ≤ P.card := Finset.card_pos.mpr h.1
  change (p.1 + -((P.image Prod.fst).min' (h.1.image _)),p.2 + -((P.image Prod.snd).min' (h.1.image _))) = q at hpq
  have hxq := congrArg Prod.fst hpq
  have hyq := congrArg Prod.snd hpq
  dsimp at hxq hyq hxeq hyeq
  omega

theorem normalized_eleven_in_box {P : Finset GridPoint} (h : EdgeConnected P)
    (hc : P.card = 11) (q : GridPoint) (hq : q ∈ normalize P h.1) :
    0 ≤ q.1 ∧ q.1 ≤ 10 ∧ 0 ≤ q.2 ∧ q.2 ≤ 10 := by
  have hb := normalized_coordinate_bound h q hq
  rw [hc] at hb
  exact hb
end Polyomino57
