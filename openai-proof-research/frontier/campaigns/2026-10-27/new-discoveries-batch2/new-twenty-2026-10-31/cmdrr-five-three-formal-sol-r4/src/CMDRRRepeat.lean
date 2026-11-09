import CMDRRRows

namespace CMDRR
variable {M W O : Type} [Fintype O]
namespace Game
 theorem women_symm (g : Game M W) (w v) : g.Women w v ↔ g.Women v w := by
  constructor <;> rintro ⟨a,ha,b,hb,hw,hv,hab⟩ <;>
    exact ⟨b,hb,a,ha,hv,hw,Ne.symm hab⟩
end Game
namespace Source
variable {s : Matching M W} {d : Schedule M W O} (h : Source s d)

 include h in
 theorem repeated_women_single {u v : W} (huv : u ≠ v)
    (hc : count (fun o => (d.game o).Women u v) ≠ 1) :
    s.SingleWoman u ∧ s.SingleWoman v := by
  constructor
  · rintro ⟨m,hm⟩
    exact hc (h.2.2.2.1 u ⟨m,hm⟩ v (Ne.symm huv))
  · rintro ⟨m,hm⟩
    have he := h.2.2.2.1 v ⟨m,hm⟩ u huv
    have hs := count_congr (fun o => (d.game o).women_symm u v)
    exact hc (hs.trans he)

/-- A two-cycle of an actual row permutation repeats opposition of its
female pair in two distinct source occurrences. Both must be single. -/
 theorem row_twoCycle_single (x y : Cell s) (hxy : x ≠ y)
    (hx : h.U x = y) (hy : h.U y = x) :
    s.SingleWoman x.1.2 ∧ s.SingleWoman y.1.2 := by
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
  apply h.repeated_women_single hf
  intro hc
  obtain ⟨o,_,ho⟩ := (count_eq_one_iff _).mp hc
  exact hab ((ho _ hoa).trans (ho _ hob).symm)
end Source
end CMDRR
