import CMDRRCentralIdentity
open scoped Classical
namespace CMDRR.Source
variable {O : Type} [Fintype O] {d : Schedule (Fin 5) (Fin 5) O}
variable (h : Source canonical d)

theorem twoCycle_single_invariant (x y : Cell canonical)
    (hx : h.U x = y) (hy : h.U y = x) (hx3 : x.1.2 = 3) (hy4 : y.1.2 = 4)
    (w : Row (s := canonical) x.1.1) :
    (3 ≤ w.1.val ↔ 3 ≤ (h.rowPerm x.1.1 w).1.val) := by
  have hm : y.1.1 = x.1.1 := by
    have hh := h.U_first x
    rw [hx] at hh
    exact hh
  have ex : ∀ v : Row (s := canonical) x.1.1, v.1 = 3 → rowCell x.1.1 v = x := by
    intro v hv
    exact Subtype.ext (Prod.ext rfl (hv.trans hx3.symm))
  have ey : ∀ v : Row (s := canonical) x.1.1, v.1 = 4 → rowCell x.1.1 v = y := by
    intro v hv
    exact Subtype.ext (Prod.ext hm.symm (hv.trans hy4.symm))
  have cases_single : ∀ v : Fin 5, 3 ≤ v.val → v = 3 ∨ v = 4 := by
    intro v hv
    exact canonical_singleWomen v ((canonical_singleWoman v).mpr hv)
  constructor
  · intro hw
    rcases cases_single w.1 hw with hw | hw
    · have he := h.rowCell_perm x.1.1 w
      rw [ex w hw,hx] at he
      have hv := congrArg (fun c : Cell canonical => c.1.2) he
      change (h.rowPerm x.1.1 w).1 = y.1.2 at hv
      rw [hv,hy4]
      decide
    · have he := h.rowCell_perm x.1.1 w
      rw [ey w hw,hy] at he
      have hv := congrArg (fun c : Cell canonical => c.1.2) he
      change (h.rowPerm x.1.1 w).1 = x.1.2 at hv
      rw [hv,hx3]
      decide
  · intro hw
    rcases cases_single (h.rowPerm x.1.1 w).1 hw with hw | hw
    · have he := ex (h.rowPerm x.1.1 w) hw
      rw [h.rowCell_perm] at he
      have hf : rowCell x.1.1 w = y := h.U.injective (he.trans hy.symm)
      have hv := congrArg (fun c : Cell canonical => c.1.2) hf
      change w.1 = y.1.2 at hv
      rw [hv,hy4]
      decide
    · have he := ey (h.rowPerm x.1.1 w) hw
      rw [h.rowCell_perm] at he
      have hf : rowCell x.1.1 w = x := h.U.injective (he.trans hx.symm)
      have hv := congrArg (fun c : Cell canonical => c.1.2) hf
      change w.1 = x.1.2 at hv
      rw [hv,hx3]
      decide

theorem twoCycle_game_partition (x y : Cell canonical)
    (hx : h.U x = y) (hy : h.U y = x) (hx3 : x.1.2 = 3) (hy4 : y.1.2 = 4)
    (o : O) (hm : ∃ w, (d.game o).Partners x.1.1 w) :
    (d.game o).Women 3 4 ∨ ∀ t ∈ (d.game o).teams, t.2.val < 3 := by
  obtain ⟨w,hw⟩ := hm
  let v : Row (s := canonical) x.1.1 := ⟨w,h.allowed hw⟩
  have ho : h.rowOccurrence x.1.1 v = o :=
    h.occurrence_eq (h.rowOccurrence_partner x.1.1 v) hw
  have hi := h.twoCycle_single_invariant x y hx hy hx3 hy4 v
  by_cases hs : 3 ≤ w.val
  · apply Or.inl
    apply (d.game o).all_singles.mp
    rw [← ho]
    apply (h.rowOccurrence_all x.1.1 v (fun w : Fin 5 => 3 ≤ w.val)).mpr
    exact ⟨hs,hi.mp hs⟩
  · apply Or.inr
    rw [← ho]
    apply (h.rowOccurrence_all x.1.1 v (fun w : Fin 5 => w.val < 3)).mpr
    exact ⟨by change w.val < 3; omega,
      Nat.lt_of_not_ge (fun hh => hs (hi.mpr hh))⟩

theorem B_add_z_of_single_twoCycle (x y : Cell canonical)
    (hx : h.U x = y) (hy : h.U y = x) (hx3 : x.1.2 = 3) (hy4 : y.1.2 = 4)
    (hm : 3 ≤ x.1.1.val) : B d + z d = 2 := by
  have hp := count_partition (fun o => (d.game o).Men 3 4)
    (fun o => ∃ w v : Fin 5, w.val < 3 ∧ v.val < 3 ∧ (d.game o).Women w v)
  have he : count (fun o => (d.game o).Men 3 4 ∧
      ¬ ∃ w v : Fin 5, w.val < 3 ∧ v.val < 3 ∧ (d.game o).Women w v) = z d := by
    apply count_congr
    intro o
    constructor
    · rintro ⟨hmen,hn⟩
      have hparticipates : ∃ w, (d.game o).Partners x.1.1 w := by
        obtain ⟨a,ha,b,hb,ha3,hb4,_⟩ := hmen
        rcases canonical_singleMen x.1.1 ((canonical_singleMan _).mpr hm) with hm3 | hm4
        · exact ⟨a.2,by change (x.1.1,a.2) ∈ (d.game o).teams; rw [hm3,← ha3]; exact ha⟩
        · exact ⟨b.2,by change (x.1.1,b.2) ∈ (d.game o).teams; rw [hm4,← hb4]; exact hb⟩
      rcases h.twoCycle_game_partition x y hx hy hx3 hy4 o hparticipates with hs | hh
      · exact ⟨hmen,hs⟩
      · exact (hn ((d.game o).all_married.mp hh)).elim
    · rintro ⟨hmen,hws⟩
      refine ⟨hmen,?_⟩
      intro hh
      have hall := (d.game o).all_married.mpr hh
      obtain ⟨a,ha,b,hb,ha3,_,_⟩ := hws
      have hc := hall a ha
      rw [ha3] at hc
      omega
  change B d + _ = _ at hp
  rw [he,h.canonical_men_repeat] at hp
  exact hp

theorem no_oriented_single_twoCycle (x y : Cell canonical) (hxy : x ≠ y)
    (hx : h.U x = y) (hy : h.U y = x) (hx3 : x.1.2 = 3) (hy4 : y.1.2 = 4)
    (hm : 3 ≤ x.1.1.val) : False := by
  have ha := h.A_zero_of_single_twoCycle x y hxy hx hy hx3 hy4 hm
  have hb := h.B_add_z_of_single_twoCycle x y hx hy hx3 hy4 hm
  have hc := h.central_incidence_identity
  omega

theorem no_single_twoCycle (x y : Cell canonical) (hxy : x ≠ y)
    (hx : h.U x = y) (hy : h.U y = x) (hm : 3 ≤ x.1.1.val) : False := by
  have hs := h.row_twoCycle_single x y hxy hx hy
  have hne : x.1.2 ≠ y.1.2 := by
    have hh := h.U_second_ne x
    rw [hx] at hh
    exact hh.symm
  have hmy : y.1.1 = x.1.1 := by
    have hh := h.U_first x
    rw [hx] at hh
    exact hh
  rcases canonical_singleWomen x.1.2 hs.1 with hx3 | hx4 <;>
    rcases canonical_singleWomen y.1.2 hs.2 with hy3 | hy4
  · exact (hne (hx3.trans hy3.symm)).elim
  · exact h.no_oriented_single_twoCycle x y hxy hx hy hx3 hy4 hm
  · exact h.no_oriented_single_twoCycle y x hxy.symm hy hx hy3 hx4 (by rw [hmy]; exact hm)
  · exact (hne (hx4.trans hy4.symm)).elim
end CMDRR.Source
