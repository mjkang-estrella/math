import SpectralLIntertwine
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ActualSpectra330264
theorem line_charpoly : LG.charpoly = LH.charpoly := charpoly_of_intertwiner _ _ LP LQ L_pq L_qp L_intertwine
#print axioms line_charpoly


theorem connectedG : G.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable G).mpr
  refine ⟨0, ?_⟩
  have r0 : G.Reachable 0 0 := SimpleGraph.Reachable.refl _
  have r1 : G.Reachable 0 1 := r0.trans (SimpleGraph.Adj.reachable (show G.Adj 0 1 from by decide +kernel))
  have r10 : G.Reachable 0 10 := r0.trans (SimpleGraph.Adj.reachable (show G.Adj 0 10 from by decide +kernel))
  have r2 : G.Reachable 0 2 := r1.trans (SimpleGraph.Adj.reachable (show G.Adj 1 2 from by decide +kernel))
  have r9 : G.Reachable 0 9 := r1.trans (SimpleGraph.Adj.reachable (show G.Adj 1 9 from by decide +kernel))
  have r11 : G.Reachable 0 11 := r10.trans (SimpleGraph.Adj.reachable (show G.Adj 10 11 from by decide +kernel))
  have r3 : G.Reachable 0 3 := r2.trans (SimpleGraph.Adj.reachable (show G.Adj 2 3 from by decide +kernel))
  have r12 : G.Reachable 0 12 := r11.trans (SimpleGraph.Adj.reachable (show G.Adj 11 12 from by decide +kernel))
  have r17 : G.Reachable 0 17 := r11.trans (SimpleGraph.Adj.reachable (show G.Adj 11 17 from by decide +kernel))
  have r4 : G.Reachable 0 4 := r3.trans (SimpleGraph.Adj.reachable (show G.Adj 3 4 from by decide +kernel))
  have r13 : G.Reachable 0 13 := r12.trans (SimpleGraph.Adj.reachable (show G.Adj 12 13 from by decide +kernel))
  have r18 : G.Reachable 0 18 := r17.trans (SimpleGraph.Adj.reachable (show G.Adj 17 18 from by decide +kernel))
  have r5 : G.Reachable 0 5 := r4.trans (SimpleGraph.Adj.reachable (show G.Adj 4 5 from by decide +kernel))
  have r14 : G.Reachable 0 14 := r13.trans (SimpleGraph.Adj.reachable (show G.Adj 13 14 from by decide +kernel))
  have r6 : G.Reachable 0 6 := r5.trans (SimpleGraph.Adj.reachable (show G.Adj 5 6 from by decide +kernel))
  have r8 : G.Reachable 0 8 := r5.trans (SimpleGraph.Adj.reachable (show G.Adj 5 8 from by decide +kernel))
  have r15 : G.Reachable 0 15 := r14.trans (SimpleGraph.Adj.reachable (show G.Adj 14 15 from by decide +kernel))
  have r7 : G.Reachable 0 7 := r6.trans (SimpleGraph.Adj.reachable (show G.Adj 6 7 from by decide +kernel))
  have r16 : G.Reachable 0 16 := r15.trans (SimpleGraph.Adj.reachable (show G.Adj 15 16 from by decide +kernel))
  intro v
  fin_cases v
  · exact r0
  · exact r1
  · exact r2
  · exact r3
  · exact r4
  · exact r5
  · exact r6
  · exact r7
  · exact r8
  · exact r9
  · exact r10
  · exact r11
  · exact r12
  · exact r13
  · exact r14
  · exact r15
  · exact r16
  · exact r17
  · exact r18
theorem treeG : G.IsTree := by
  apply (SimpleGraph.isTree_iff_connected_and_card).mpr
  refine ⟨connectedG, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  decide +kernel
#print axioms treeG

theorem connectedH : H.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable H).mpr
  refine ⟨0, ?_⟩
  have r0 : H.Reachable 0 0 := SimpleGraph.Reachable.refl _
  have r1 : H.Reachable 0 1 := r0.trans (SimpleGraph.Adj.reachable (show H.Adj 0 1 from by decide +kernel))
  have r11 : H.Reachable 0 11 := r0.trans (SimpleGraph.Adj.reachable (show H.Adj 0 11 from by decide +kernel))
  have r2 : H.Reachable 0 2 := r1.trans (SimpleGraph.Adj.reachable (show H.Adj 1 2 from by decide +kernel))
  have r12 : H.Reachable 0 12 := r11.trans (SimpleGraph.Adj.reachable (show H.Adj 11 12 from by decide +kernel))
  have r3 : H.Reachable 0 3 := r2.trans (SimpleGraph.Adj.reachable (show H.Adj 2 3 from by decide +kernel))
  have r9 : H.Reachable 0 9 := r2.trans (SimpleGraph.Adj.reachable (show H.Adj 2 9 from by decide +kernel))
  have r13 : H.Reachable 0 13 := r12.trans (SimpleGraph.Adj.reachable (show H.Adj 12 13 from by decide +kernel))
  have r18 : H.Reachable 0 18 := r12.trans (SimpleGraph.Adj.reachable (show H.Adj 12 18 from by decide +kernel))
  have r4 : H.Reachable 0 4 := r3.trans (SimpleGraph.Adj.reachable (show H.Adj 3 4 from by decide +kernel))
  have r10 : H.Reachable 0 10 := r9.trans (SimpleGraph.Adj.reachable (show H.Adj 9 10 from by decide +kernel))
  have r14 : H.Reachable 0 14 := r13.trans (SimpleGraph.Adj.reachable (show H.Adj 13 14 from by decide +kernel))
  have r5 : H.Reachable 0 5 := r4.trans (SimpleGraph.Adj.reachable (show H.Adj 4 5 from by decide +kernel))
  have r15 : H.Reachable 0 15 := r14.trans (SimpleGraph.Adj.reachable (show H.Adj 14 15 from by decide +kernel))
  have r6 : H.Reachable 0 6 := r5.trans (SimpleGraph.Adj.reachable (show H.Adj 5 6 from by decide +kernel))
  have r8 : H.Reachable 0 8 := r5.trans (SimpleGraph.Adj.reachable (show H.Adj 5 8 from by decide +kernel))
  have r16 : H.Reachable 0 16 := r15.trans (SimpleGraph.Adj.reachable (show H.Adj 15 16 from by decide +kernel))
  have r7 : H.Reachable 0 7 := r6.trans (SimpleGraph.Adj.reachable (show H.Adj 6 7 from by decide +kernel))
  have r17 : H.Reachable 0 17 := r16.trans (SimpleGraph.Adj.reachable (show H.Adj 16 17 from by decide +kernel))
  intro v
  fin_cases v
  · exact r0
  · exact r1
  · exact r2
  · exact r3
  · exact r4
  · exact r5
  · exact r6
  · exact r7
  · exact r8
  · exact r9
  · exact r10
  · exact r11
  · exact r12
  · exact r13
  · exact r14
  · exact r15
  · exact r16
  · exact r17
  · exact r18
theorem treeH : H.IsTree := by
  apply (SimpleGraph.isTree_iff_connected_and_card).mpr
  refine ⟨connectedH, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  decide +kernel
#print axioms treeH

end ActualSpectra330264
