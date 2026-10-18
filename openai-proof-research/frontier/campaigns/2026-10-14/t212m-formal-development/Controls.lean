import T212M
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

namespace T212MControls
open T212M

noncomputable def lineDistance (u v : Fin 4) : ℝ := |(u : ℝ) - (v : ℝ)|
noncomputable def lineWeight : Sym2 (Fin 4) → ℝ :=
  Sym2.lift ⟨lineDistance, fun u v => abs_sub_comm (u : ℝ) (v : ℝ)⟩
def changedEdges : Finset (Sym2 (Fin 4)) := {s(0, 1)}
noncomputable def newWeight (e : Sym2 (Fin 4)) : ℝ :=
  if e ∈ changedEdges then lineWeight e - 1/2 else lineWeight e

def segment : (⊤ : SimpleGraph (Fin 4)).Walk 2 3 :=
  SimpleGraph.Walk.cons (by decide) SimpleGraph.Walk.nil

theorem line_triangle (u v z : Fin 4) :
    lineDistance u z ≤ lineDistance u v + lineDistance v z :=
  abs_sub_le _ _ _

theorem line_dominates {u v : Fin 4} (p : (⊤ : SimpleGraph (Fin 4)).Walk u v) :
    lineDistance u v ≤ walkCost lineWeight p := by
  apply distance_dominated_by_cost lineDistance _ line_triangle lineWeight _ p
  · intro a; simp [lineDistance]
  · intro a b h; exact le_rfl

theorem late_segment_example {p : (⊤ : SimpleGraph (Fin 4)).Walk 2 3}
    (hp : p.edges.Nodup) : walkCost newWeight segment ≤ walkCost newWeight p := by
  apply late_segment_minimizes lineDistance (fun u v => abs_sub_comm (u : ℝ) (v : ℝ)) line_triangle
    lineWeight newWeight changedEdges _ (fun q => line_dominates q) (x := 0) 0
    _ _ _ segment _ _ p hp
  · intro e he; simp [newWeight, he]
  · intro e he
    have : e = s(0, 1) := by simpa [changedEdges] using he
    subst e
    exact ⟨0, by simp, by simp [lineDistance]⟩
  · norm_num [lineDistance]
  · norm_num [changeBudget, changedEdges, newWeight, lineWeight, lineDistance]
  · norm_num [segment, walkCost, lineWeight, lineDistance]
  · intro e he
    have : e = s(2, 3) := by simpa [segment] using he
    subst e
    decide

def repeatedEdge : (⊤ : SimpleGraph (Fin 4)).Walk 0 1 :=
  SimpleGraph.Walk.cons (v := 1) (by decide)
    (SimpleGraph.Walk.cons (v := 0) (by decide)
      (SimpleGraph.Walk.cons (v := 1) (by decide) SimpleGraph.Walk.nil))

theorem repeated_edge_breaks_single_budget :
    ¬ |walkCost newWeight repeatedEdge - walkCost lineWeight repeatedEdge| ≤
      changeBudget changedEdges lineWeight newWeight := by
  norm_num [repeatedEdge, walkCost, changeBudget, newWeight, changedEdges,
    lineWeight, lineDistance]

def earlySegment : (⊤ : SimpleGraph (Fin 4)).Walk 0 2 :=
  .cons (by decide) .nil

def shortcut : (⊤ : SimpleGraph (Fin 4)).Walk 0 2 :=
  SimpleGraph.Walk.cons (v := 1) (by decide)
    (SimpleGraph.Walk.cons (v := 2) (by decide) SimpleGraph.Walk.nil)

theorem early_segment_is_old_minimal {p : (⊤ : SimpleGraph (Fin 4)).Walk 0 2} :
    walkCost lineWeight earlySegment ≤ walkCost lineWeight p := by
  have h := line_dominates p
  simpa [walkCost, earlySegment, lineWeight, lineDistance] using h

theorem early_segment_unchanged :
    walkCost newWeight earlySegment = walkCost lineWeight earlySegment := by
  norm_num [walkCost, earlySegment, newWeight, changedEdges, lineWeight, lineDistance]

theorem without_lateness_minimality_fails :
    walkCost newWeight shortcut < walkCost newWeight earlySegment := by
  norm_num [walkCost, shortcut, earlySegment, newWeight, changedEdges,
    lineWeight, lineDistance]

end T212MControls
