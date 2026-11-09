import CMDRRNormalize
import CMDRRSingleCounts

open scoped Classical
namespace CMDRR.Source
variable {M W O : Type} [Fintype O]
variable {s : Matching M W} {d : Schedule M W O} (h : Source s d)
abbrev Row (m : M) := {w : W // ¬ s.spouse m w}
def rowCell (m : M) (w : Row (s := s) m) : Cell s := ⟨(m,w.1),w.2⟩
noncomputable def rowMap (m : M) (w : Row (s := s) m) : Row (s := s) m :=
  ⟨(h.U (rowCell m w)).1.2, by
    have hu := (h.U (rowCell m w)).2
    rw [h.U_first] at hu
    exact hu⟩
theorem rowCell_map (m : M) (w : Row (s := s) m) :
    rowCell m (h.rowMap m w) = h.U (rowCell m w) := by
  apply Subtype.ext
  apply Prod.ext
  · exact (h.U_first (rowCell m w)).symm
  · rfl

theorem rowMap_bijective (m : M) : Function.Bijective (h.rowMap m) := by
  constructor
  · intro a b hab
    have he := congrArg (rowCell (s := s) m) hab
    rw [h.rowCell_map,h.rowCell_map] at he
    exact Subtype.ext (congrArg (fun x : Cell s => x.1.2) (h.U.injective he))
  · intro w
    let x := h.U.symm (rowCell (s := s) m w)
    have hf : x.1.1 = m := by
      have hh := h.U_first x
      change (h.U (h.U.symm (rowCell m w))).1.1 = x.1.1 at hh
      rw [Equiv.apply_symm_apply] at hh
      exact hh.symm
    let a : Row (s := s) m := ⟨x.1.2, by rw [← hf]; exact x.2⟩
    have he : rowCell m a = x := Subtype.ext (Prod.ext hf.symm rfl)
    refine ⟨a,?_⟩
    apply Subtype.ext
    change (h.U (rowCell m a)).1.2 = w.1
    rw [he]
    change (h.U (h.U.symm (rowCell m w))).1.2 = w.1
    rw [Equiv.apply_symm_apply]
    rfl
noncomputable def rowPerm (m : M) : Equiv.Perm (Row (s := s) m) :=
  Equiv.ofBijective (h.rowMap m) (h.rowMap_bijective m)
theorem rowPerm_no_fixed (m : M) (w : Row (s := s) m) : h.rowPerm m w ≠ w := by
  intro he
  exact h.U_second_ne (rowCell m w) (congrArg Subtype.val he)
theorem rowCell_perm (m : M) (w : Row (s := s) m) :
    rowCell m (h.rowPerm m w) = h.U (rowCell m w) := h.rowCell_map m w
end CMDRR.Source
