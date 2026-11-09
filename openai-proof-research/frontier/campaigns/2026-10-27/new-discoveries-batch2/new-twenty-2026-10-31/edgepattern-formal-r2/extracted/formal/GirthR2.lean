import ConcreteR2
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
namespace EdgePattern.Concrete

def bicoloring : graph.Coloring Bool where
  toFun := ![false,true,true,true,false,false,true,false]
  map_rel' := by decide

theorem no_four : ∀ a b c d : V, a ≠ c → b ≠ d →
    graph.Adj a b → graph.Adj b c → graph.Adj c d → ¬ graph.Adj d a := by decide

theorem girth_at_least : GirthAtLeast pattern 6 := by
  intro v c hc
  have he : Even c.length := bicoloring.even_length_iff_congr c |>.mpr Iff.rfl
  have h3 : 3 ≤ c.length := hc.three_le_length
  obtain ⟨k,hk⟩ := he
  by_contra hn
  have h4 : c.length = 4 := by omega
  have hcopy : SimpleGraph.IsContained (SimpleGraph.cycleGraph 4) graph :=
    (SimpleGraph.cycleGraph_isContained_iff (by decide)).mpr ⟨v,c,hc,h4⟩
  obtain ⟨f⟩ := hcopy
  exact no_four (f 0) (f 1) (f 2) (f 3)
    (fun h => (by decide : (0 : Fin 4) ≠ 2) (f.injective h))
    (fun h => (by decide : (1 : Fin 4) ≠ 3) (f.injective h))
    (f.toHom.map_rel' (by decide)) (f.toHom.map_rel' (by decide))
    (f.toHom.map_rel' (by decide)) (f.toHom.map_rel' (by decide))

def sixCycle : graph.Walk 0 0 :=
  .cons (by decide : graph.Adj 0 1) <|
  .cons (by decide : graph.Adj 1 5) <|
  .cons (by decide : graph.Adj 5 6) <|
  .cons (by decide : graph.Adj 6 4) <|
  .cons (by decide : graph.Adj 4 3) <|
  .cons (by decide : graph.Adj 3 0) .nil

theorem sixCycle_isCycle : sixCycle.IsCycle := by
  apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · rw [SimpleGraph.Walk.isPath_def]
    decide
  · decide

theorem exact_girth : ExactGirth pattern 6 :=
  ⟨girth_at_least, 0, sixCycle, sixCycle_isCycle, rfl⟩
end EdgePattern.Concrete
