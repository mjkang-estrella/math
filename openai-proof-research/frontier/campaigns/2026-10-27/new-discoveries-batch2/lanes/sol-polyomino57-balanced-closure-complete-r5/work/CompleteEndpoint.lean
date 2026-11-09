import SuffixAssembly
import Stage7Closed
import Stage8Closed
import Stage9Closed
import Stage10Closed
import TerminalFamilyPlaced
import TreeAll
set_option autoImplicit false
namespace Polyomino57
theorem family11_fixed : family11 = terminalRowTree := by rfl
def completeFamily (n : ℕ) (row : List GridPoint) : Prop :=
  match n with
  | 7 => FamilyMember row family7
  | 8 => FamilyMember row family8
  | 9 => FamilyMember row family9
  | 10 => FamilyMember row family10
  | _ => FamilyMember row family11
 theorem completeFamily_steps : ∀ n, 7 ≤ n → n < 11 → ∀ row,
    completeFamily n row → FamilyRowClosed (completeFamily (n+1)) row := by
  intro n hlo hhi row h
  have hn : n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 := by omega
  rcases hn with rfl | rfl | rfl | rfl
  · exact stage7_closed row h
  · exact stage8_closed row h
  · exact stage9_closed row h
  · exact stage10_closed row h
 theorem universalContainer11_witness : UniversalContainer 11 witness := by
  refine ⟨witness_connected, ?_⟩
  intro P hP hc
  obtain ⟨row,hm,hr,he⟩ := coverage_after_seven completeFamily
    family7_of_layer7 completeFamily_steps (growth_complete hP) (by omega) (by omega)
  rw [hc] at hm
  obtain ⟨t,ht⟩ := terminal_family_placed row hm
  exact placement_of_normalized_row P hP.1 (row,t) hr he ht
 theorem not_SourceFormula : ¬ SourceFormula :=
  refute_of_container witness witness_card universalContainer11_witness
 theorem minimumSize11_le_57 : minimumSize 11 ≤ 57 :=
  minimumSize_le ⟨witness,witness_card,universalContainer11_witness⟩
end Polyomino57
