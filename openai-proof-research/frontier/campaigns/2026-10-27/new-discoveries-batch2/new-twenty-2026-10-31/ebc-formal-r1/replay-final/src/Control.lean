import Definitions
namespace EBC337062
open SimpleGraph
abbrev G2 := circ 2 1 1 1

theorem control_edge : s((0 : ZMod 2), 1) ∈ G2.edgeSet := by decide

theorem control_unique_edge (e : Sym2 (ZMod 2)) (h : e ∈ G2.edgeSet) :
    e = s(0,1) := by
  revert h
  refine Sym2.inductionOn e (fun a b => ?_)
  fin_cases a <;> fin_cases b <;> decide

theorem control_uniform : EdgeBetweennessUniform G2 := by
  intro e he f hf
  rw [control_unique_edge e he, control_unique_edge f hf]

theorem control_edgeTransitive : EdgeTransitive G2 := by
  intro e he f hf
  refine ⟨SimpleGraph.Iso.refl, ?_⟩
  rw [control_unique_edge e he, control_unique_edge f hf]
  rfl
end EBC337062
