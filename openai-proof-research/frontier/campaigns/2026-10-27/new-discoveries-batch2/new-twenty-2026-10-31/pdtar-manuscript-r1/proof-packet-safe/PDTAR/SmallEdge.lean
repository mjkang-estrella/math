import PDTAR.CoreProofLocal
namespace PDTAR
set_option linter.unusedSectionVars false
open Finset
variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem noIsolated_iso {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : NoIsolated G) (e : G ≃g H) : NoIsolated H := by
  intro v
  obtain ⟨w,hw⟩ := hG (e.symm v)
  refine ⟨e w, ?_⟩
  have hh := e.map_rel_iff.mpr hw
  simpa using hh

/-- Equal PD families give a TAR isomorphism by the identity on finsets. -/
noncomputable def samePD_tar_iso {G H : SimpleGraph V} (he : SamePD G H) :
    tar G ≃g tar H where
  toFun S := ⟨S.val,(he S.val).mp S.property⟩
  invFun S := ⟨S.val,(he S.val).mpr S.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- A two-vertex simple graph with no isolated vertices is the edge. -/
theorem small_edge_rigid (H : SimpleGraph (Fin 1 ⊕ Fin 1)) (hH : NoIsolated H) :
    H = completeBipartiteGraph (Fin 1) (Fin 1) := by
  have he : H.Adj (Sum.inl 0) (Sum.inr 0) := by
    obtain ⟨w,hw⟩ := hH (Sum.inl 0)
    rcases w with w | w
    · fin_cases w; exact False.elim (H.irrefl hw)
    · fin_cases w; exact hw
  ext x y
  rcases x with x | x <;> rcases y with y | y <;> fin_cases x <;> fin_cases y
  · simp [completeBipartiteGraph]
  · simp [completeBipartiteGraph, he]
  · simp [completeBipartiteGraph, he.symm]
  · simp [completeBipartiteGraph]

theorem small_edge_of_reduction (hR : ReductionRemaining) : EdgeRemaining := by
  intro W _ _ H hH hiso
  have hK : NoIsolated (completeBipartiteGraph (Fin 1) (Fin 1)) := by
    intro v
    rcases v with v | v
    · exact ⟨Sum.inr 0,by simp [completeBipartiteGraph]⟩
    · exact ⟨Sum.inl 0,by simp [completeBipartiteGraph]⟩
  obtain ⟨H',⟨e⟩,_⟩ := hR _ _ _ H hK hH hiso
  have heq := small_edge_rigid H' (noIsolated_iso hH e)
  subst H'
  exact ⟨e⟩
end PDTAR
