import CMDRRRowDegree

namespace CMDRR
variable {M W O : Type} [Fintype O]
namespace Source
variable {s : Matching M W} {d : Schedule M W O} (h : Source s d)
theorem row_twoCycle_games (x y : Cell s) (hxy : x ≠ y)
    (hx : h.U x = y) (hy : h.U y = x) :
    ∃ o p : O, o ≠ p ∧ (d.game o).Women x.1.2 y.1.2 ∧
      (d.game p).Women x.1.2 y.1.2 ∧
      (∃ w, (d.game o).Partners x.1.1 w) ∧
      (∃ w, (d.game p).Partners x.1.1 w) := by
  obtain ⟨a,rfl⟩ := h.cellsEquiv.surjective x
  obtain ⟨b,rfl⟩ := h.cellsEquiv.surjective y
  have hm : a.2.1.1 = b.2.1.1 := by
    have he := h.U_first (h.cellsEquiv a)
    rw [hx] at he
    exact he.symm
  have hf : a.2.1.2 ≠ b.2.1.2 := by
    intro he
    exact hxy (Subtype.ext (Prod.ext hm he))
  have hax : ((d.game a.1).other a.2).1.2 = b.2.1.2 := by
    have he := congrArg (fun c : Cell s => c.1.2) hx
    rw [h.U_incidence] at he
    exact he
  have hby : ((d.game b.1).other b.2).1.2 = a.2.1.2 := by
    have he := congrArg (fun c : Cell s => c.1.2) hy
    rw [h.U_incidence] at he
    exact he
  have hoa : (d.game a.1).Women a.2.1.2 b.2.1.2 :=
    ⟨_,a.2.2,_,((d.game a.1).other a.2).2,rfl,hax,
      fun he => (d.game a.1).other_ne a.2 (Subtype.ext he.symm)⟩
  have hob : (d.game b.1).Women a.2.1.2 b.2.1.2 :=
    ⟨_,((d.game b.1).other b.2).2,_,b.2.2,hby,rfl,
      fun he => (d.game b.1).other_ne b.2 (Subtype.ext he)⟩
  have hab : a.1 ≠ b.1 := by
    intro he
    have hb : b.2.1 ∈ (d.game a.1).teams := by
      rw [he]
      exact b.2.2
    have hp : (d.game a.1).Partners a.2.1.1 a.2.1.2 := a.2.2
    have hq : (d.game a.1).Partners a.2.1.1 b.2.1.2 := by
      rw [hm]
      exact hb
    exact hf ((d.game a.1).partner_unique_woman hp hq)
  refine ⟨a.1,b.1,hab,hoa,hob,⟨a.2.1.2,a.2.2⟩,b.2.1.2,?_⟩
  change (d.game b.1).Partners a.2.1.1 b.2.1.2
  rw [hm]
  exact b.2.2
end Source

 theorem count_two_exhaust (p : O → Prop) (hc : count p = 2)
    {a b : O} (hab : a ≠ b) (ha : p a) (hb : p b) :
    ∀ o, p o → o = a ∨ o = b := by
  classical
  let S := Finset.univ.filter p
  have hs : S.card = 2 := hc
  have he : ({a,b} : Finset O) = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [S,ha,hb]
    · simp [hs,hab]
  intro o ho
  have hh : o ∈ S := by simp [S,ho]
  rw [← he] at hh
  simpa using hh
end CMDRR
