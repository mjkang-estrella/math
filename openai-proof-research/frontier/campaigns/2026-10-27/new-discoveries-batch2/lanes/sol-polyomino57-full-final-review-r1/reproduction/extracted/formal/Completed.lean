import Empty00
import Empty01
import Empty02
import Empty03
import Empty04
import Empty05
import Empty06
import Empty07
import Empty08
import Empty09
import Empty10
import Empty11
import Empty12
import Empty13
import Empty14
import Empty15
import Empty16
import Empty17
import Empty18
import Empty19
import Empty20
import Empty21
import Empty22
import Empty23
import Empty24
import Empty25
import Empty26
import Empty27
import Empty28
import Empty29
import Empty30
import Empty31
import Empty32
import Empty33
import Empty34
import Forced730
import SmallCase
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Polyomino57.Diagonal.FiniteProof
open Polyomino57
def completed : Finset (ℤ × ℤ × ℤ) := {(1,1,0),(2,1,0),(2,2,0),(2,2,1),(3,1,0),(3,2,0),(3,3,0),(4,1,0),(4,2,0),(4,2,1),(4,3,0),(4,4,0),(4,4,1),(5,1,0),(5,2,0),(5,3,0),(5,4,0),(5,5,0),(6,1,0),(6,2,0),(6,2,1),(6,3,0),(6,4,0),(6,4,1),(6,5,0),(6,6,0),(7,1,0),(7,2,0),(8,1,0),(8,2,0),(8,2,1),(9,1,0),(9,2,0),(10,1,0),(10,2,0),(7,3,0),(10,10,1)}
theorem completed_card : completed.card = 37 := by decide
theorem completed_canonical : completed ⊆ canonicalCases := by decide
theorem completed_cases : ∀ c ∈ completed, ∀ Q : Finset GridPoint,
    Q ⊆ domain c.1 c.2.1 c.2.2 → EdgeConnected Q → Q.card = 11 →
    ¬ HitsAll Q (groups c.1 c.2.1 c.2.2) := by
  intro c hc
  simp only [completed, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact case_1_1_0
  · exact case_2_1_0
  · exact case_2_2_0
  · exact case_2_2_1
  · exact case_3_1_0
  · exact case_3_2_0
  · exact case_3_3_0
  · exact case_4_1_0
  · exact case_4_2_0
  · exact case_4_2_1
  · exact case_4_3_0
  · exact case_4_4_0
  · exact case_4_4_1
  · exact case_5_1_0
  · exact case_5_2_0
  · exact case_5_3_0
  · exact case_5_4_0
  · exact case_5_5_0
  · exact case_6_1_0
  · exact case_6_2_0
  · exact case_6_2_1
  · exact case_6_3_0
  · exact case_6_4_0
  · exact case_6_4_1
  · exact case_6_5_0
  · exact case_6_6_0
  · exact case_7_1_0
  · exact case_7_2_0
  · exact case_8_1_0
  · exact case_8_2_0
  · exact case_8_2_1
  · exact case_9_1_0
  · exact case_9_2_0
  · exact case_10_1_0
  · exact case_10_2_0
  · exact case_7_3_0
  · exact Small.case_10_10_1
def RemainingCases : Prop :=
  ∀ c ∈ canonicalCases, c ∉ completed → ∀ Q : Finset GridPoint,
    Q ⊆ domain c.1 c.2.1 c.2.2 → EdgeConnected Q → Q.card = 11 →
    ¬ HitsAll Q (groups c.1 c.2.1 c.2.2)
theorem remaining_card : (canonicalCases \ completed).card = 33 := by decide
theorem finiteCases_iff_remaining : FiniteCases ↔ RemainingCases := by
  constructor
  · intro h c hc _; exact h c hc
  · intro h c hc
    by_cases hd : c ∈ completed
    · exact completed_cases c hd
    · exact h c hc hd
theorem universalContainer_of_remaining (h : RemainingCases) : UniversalContainer 11 witness :=
  universalContainer_of_finiteCases (finiteCases_iff_remaining.mpr h)
end Polyomino57.Diagonal.FiniteProof
