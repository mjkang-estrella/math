import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic.FinCases
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Data.Rat.Defs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ActualSpectra330264
def edgesG : List (Nat × Nat) := [(1, 0), (1, 2), (1, 9), (0, 10), (2, 3), (3, 4), (4, 5), (5, 6), (5, 8), (6, 7), (10, 11), (11, 12), (11, 17), (12, 13), (13, 14), (14, 15), (15, 16), (17, 18)]
def edgesH : List (Nat × Nat) := [(1, 0), (1, 2), (0, 11), (2, 3), (2, 9), (3, 4), (4, 5), (5, 6), (5, 8), (6, 7), (9, 10), (11, 12), (12, 13), (12, 18), (13, 14), (14, 15), (15, 16), (16, 17)]
def adjacent (es : List (Nat × Nat)) (u v : Fin 19) : Prop := (u.val, v.val) ∈ es ∨ (v.val, u.val) ∈ es
instance (es) : DecidableRel (adjacent es) := fun u v => inferInstanceAs (Decidable ((u.val, v.val) ∈ es ∨ (v.val, u.val) ∈ es))
def graph (es : List (Nat × Nat)) (hs : ∀ v : Fin 19, ¬ adjacent es v v) : SimpleGraph (Fin 19) where
  Adj := adjacent es
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨hs⟩
def G : SimpleGraph (Fin 19) := graph edgesG (by decide +kernel)
def H : SimpleGraph (Fin 19) := graph edgesH (by decide +kernel)
instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (adjacent edgesG _ _))
instance : DecidableRel H.Adj := fun _ _ => inferInstanceAs (Decidable (adjacent edgesH _ _))
def AG : Matrix (Fin 19) (Fin 19) ℚ := G.adjMatrix ℚ
def AH : Matrix (Fin 19) (Fin 19) ℚ := H.adjMatrix ℚ
def CG : Matrix (Fin 19) (Fin 19) ℚ := Gᶜ.adjMatrix ℚ
def CH : Matrix (Fin 19) (Fin 19) ℚ := Hᶜ.adjMatrix ℚ
def edgeG (i : Fin 18) : Nat × Nat := edgesG[i.val]!
def lineG : SimpleGraph (Fin 18) where
  Adj i j := i ≠ j ∧ ((edgeG i).1 = (edgeG j).1 ∨ (edgeG i).1 = (edgeG j).2 ∨ (edgeG i).2 = (edgeG j).1 ∨ (edgeG i).2 = (edgeG j).2)
  symm := ⟨by intros; aesop⟩
  loopless := ⟨by intro i; simp⟩
instance : DecidableRel lineG.Adj := fun i j => by unfold SimpleGraph.Adj lineG; infer_instance
def LG : Matrix (Fin 18) (Fin 18) ℚ := lineG.adjMatrix ℚ
def edgeH (i : Fin 18) : Nat × Nat := edgesH[i.val]!
def lineH : SimpleGraph (Fin 18) where
  Adj i j := i ≠ j ∧ ((edgeH i).1 = (edgeH j).1 ∨ (edgeH i).1 = (edgeH j).2 ∨ (edgeH i).2 = (edgeH j).1 ∨ (edgeH i).2 = (edgeH j).2)
  symm := ⟨by intros; aesop⟩
  loopless := ⟨by intro i; simp⟩
instance : DecidableRel lineH.Adj := fun i j => by unfold SimpleGraph.Adj lineH; infer_instance
def LH : Matrix (Fin 18) (Fin 18) ℚ := lineH.adjMatrix ℚ
theorem charpoly_of_intertwiner {n : ℕ} (A B P Q : Matrix (Fin n) (Fin n) ℚ)
    (hp : P * Q = 1) (hq : Q * P = 1) (hi : A * P = P * B) : A.charpoly = B.charpoly := by
  have hA : A = P * (B * Q) := by rw [← Matrix.mul_assoc, ← hi, Matrix.mul_assoc, hp, mul_one]
  rw [hA, Matrix.charpoly_mul_comm, Matrix.mul_assoc, hq, mul_one]


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
