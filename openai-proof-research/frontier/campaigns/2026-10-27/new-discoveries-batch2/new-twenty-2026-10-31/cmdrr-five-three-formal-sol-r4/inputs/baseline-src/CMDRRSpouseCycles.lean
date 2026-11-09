import CMDRRCanonical
import CMDRROrbitCard

open scoped Classical
namespace CMDRR.Source
variable {O : Type} [Fintype O] {d : Schedule (Fin 5) (Fin 5) O}
variable (h : Source canonical d)

include h in
 theorem canonical_women_repeat : count (fun o => (d.game o).Women 3 4) = 2 := by
  exact (h.unique_other_woman_count (by simp) canonical_singleWomen).1
include h in
 theorem canonical_men_repeat : count (fun o => (d.game o).Men 3 4) = 2 := by
  exact (h.unique_other_man_count (by simp) canonical_singleMen).1

 theorem canonical_row_card (m : Fin 5) (hm : m.val < 3) :
    Fintype.card (Row (s := canonical) m) = 4 := by
  classical
  change Fintype.card {w : Fin 5 // ¬ canonical.spouse m w} = 4
  simp [canonical,hm,Fintype.card_subtype_compl]

theorem row_not_two_of_married (m : Fin 5) (w : Row (s := canonical) m)
    (hw : w.1.val < 3) : h.rowPerm m (h.rowPerm m w) ≠ w := by
  intro he
  let x := rowCell (s := canonical) m w
  let y := rowCell (s := canonical) m (h.rowPerm m w)
  have hxy : x ≠ y := by
    intro hh
    apply h.rowPerm_no_fixed m w
    exact Subtype.ext (congrArg (fun c : Cell canonical => c.1.2) hh.symm)
  have hx : h.U x = y := (h.rowCell_perm m w).symm
  have hy : h.U y = x := by
    rw [← h.rowCell_perm m (h.rowPerm m w),he]
  have hs := (h.row_twoCycle_single x y hxy hx hy).1
  have hge := (canonical_singleWoman w.1).mp hs
  omega

/-- Every spouse row is one four-cycle, on its actual source-derived domain.
The witness is a non-wife married woman; her two-cycle is forbidden by the
occurrence-count restriction, and cardinality four forces the entire orbit. -/
theorem spouse_row_four (m : Fin 5) (hm : m.val < 3) :
    ∃ x c : Row (s := canonical) m,
      h.rowPerm m (h.rowPerm m (h.rowPerm m x)) = c ∧ h.rowPerm m c = x ∧
      x ≠ h.rowPerm m x ∧ x ≠ h.rowPerm m (h.rowPerm m x) ∧ x ≠ c ∧
      h.rowPerm m x ≠ h.rowPerm m (h.rowPerm m x) ∧ h.rowPerm m x ≠ c ∧
      h.rowPerm m (h.rowPerm m x) ≠ c ∧
      ∀ y, y = x ∨ y = h.rowPerm m x ∨
        y = h.rowPerm m (h.rowPerm m x) ∨ y = c := by
  classical
  obtain ⟨w,hw,hn⟩ : ∃ w : Fin 5, w.val < 3 ∧ w ≠ m := by
    by_cases hz : m = 0
    · exact ⟨1,by decide,by simp [hz]⟩
    · exact ⟨0,by decide,Ne.symm hz⟩
  let x : Row (s := canonical) m := ⟨w,fun hs => hn hs.1.symm⟩
  refine ⟨x,?_⟩
  exact orbit_four_of_not_two (h.rowPerm m) (canonical_row_card m hm)
    (h.rowPerm_no_fixed m) x (h.row_not_two_of_married m x hw)
end CMDRR.Source
