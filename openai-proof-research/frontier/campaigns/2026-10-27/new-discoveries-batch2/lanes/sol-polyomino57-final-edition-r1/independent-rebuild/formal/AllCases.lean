import Completed
import F740Case
import F830Case
import F840Case
import R6_6_1Case
import R7_5_0Case
import R7_6_0Case
import R7_7_0Case
import R8_4_1Case
import R8_5_0Case
import R8_6_0Case
import R8_6_1Case
import R8_7_0Case
import R8_8_0Case
import C8_8_1Case
import R9_3_0Case
import R9_4_0Case
import R9_5_0Case
import R9_6_0Case
import C9_7_0Case
import C9_8_0Case
import C9_9_0Case
import C10_2_1Case
import C10_3_0Case
import C10_4_0Case
import C10_4_1Case
import C10_5_0Case
import C10_6_0Case
import C10_6_1Case
import C10_7_0Case
import C10_8_0Case
import C10_8_1Case
import C10_9_0Case
import C10_10_0Case
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Polyomino57.Diagonal.FiniteProof.AllCases
open Polyomino57
def residual : Finset (ℤ × ℤ × ℤ) := {(6,6,1),(7,5,0),(7,6,0),(7,7,0),(8,4,1),(8,5,0),(8,6,0),(8,6,1),(8,7,0),(8,8,0),(8,8,1),(9,3,0),(9,4,0),(9,5,0),(9,6,0),(9,7,0),(9,8,0),(9,9,0),(10,2,1),(10,3,0),(10,4,0),(10,4,1),(10,5,0),(10,6,0),(10,6,1),(10,7,0),(10,8,0),(10,8,1),(10,9,0),(10,10,0),(7,4,0),(8,3,0),(8,4,0)}
theorem residual_eq : canonicalCases \ completed = residual := by decide
theorem remaining : RemainingCases := by
  intro c hc hn
  have hm : c ∈ residual := by
    rw [← residual_eq]
    exact Finset.mem_sdiff.mpr ⟨hc,hn⟩
  simp only [residual, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact R6_6_1.case_6_6_1
  · exact R7_5_0.case_7_5_0
  · exact R7_6_0.case_7_6_0
  · exact R7_7_0.case_7_7_0
  · exact R8_4_1.case_8_4_1
  · exact R8_5_0.case_8_5_0
  · exact R8_6_0.case_8_6_0
  · exact R8_6_1.case_8_6_1
  · exact R8_7_0.case_8_7_0
  · exact R8_8_0.case_8_8_0
  · exact C8_8_1.case_8_8_1
  · exact R9_3_0.case_9_3_0
  · exact R9_4_0.case_9_4_0
  · exact R9_5_0.case_9_5_0
  · exact R9_6_0.case_9_6_0
  · exact C9_7_0.case_9_7_0
  · exact C9_8_0.case_9_8_0
  · exact C9_9_0.case_9_9_0
  · exact C10_2_1.case_10_2_1
  · exact C10_3_0.case_10_3_0
  · exact C10_4_0.case_10_4_0
  · exact C10_4_1.case_10_4_1
  · exact C10_5_0.case_10_5_0
  · exact C10_6_0.case_10_6_0
  · exact C10_6_1.case_10_6_1
  · exact C10_7_0.case_10_7_0
  · exact C10_8_0.case_10_8_0
  · exact C10_8_1.case_10_8_1
  · exact C10_9_0.case_10_9_0
  · exact C10_10_0.case_10_10_0
  · exact F740.case_7_4_0
  · exact F830.case_8_3_0
  · exact F840.case_8_4_0
theorem finiteCases : FiniteCases := finiteCases_iff_remaining.mpr remaining
 theorem universalContainer : UniversalContainer 11 witness := universalContainer_of_remaining remaining
 theorem eligible : EligibleSize 11 57 := ⟨witness,witness_card,universalContainer⟩
 theorem minimum_le : minimumSize 11 ≤ 57 := by
  classical
  have hx : ∃ m, EligibleSize 11 m := ⟨57,eligible⟩
  unfold minimumSize
  rw [dite_eq_left hx]
  exact Nat.find_min' hx eligible
 theorem source_refutation : ¬ SourceFormula := by
  intro h
  have he := h 11 (by decide)
  have hl := minimum_le
  change minimumSize 11 = 58 at he
  omega
end Polyomino57.Diagonal.FiniteProof.AllCases
