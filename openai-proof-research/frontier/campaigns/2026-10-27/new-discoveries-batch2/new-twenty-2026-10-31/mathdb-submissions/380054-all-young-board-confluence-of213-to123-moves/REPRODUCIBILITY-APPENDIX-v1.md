# Reproducibility appendix v1

Verbatim pinned source modules. UTF-8; LF preserved.

```lean module=Young64.lean
import YoungSupportPeaks
import Mathlib.Data.Fin.VecNotation
namespace Young213

noncomputable def case1p : Placement 4 := Equiv.ofBijective (![1,0,2,3] : Fin 4 → Fin 4) (by decide)
def case1b : Fin 4 → Nat := ![0,0,0,0]
theorem case1_strongest : case1b = suffixCap (peakCaps case1p 1 2 1 3) := by
  funext i
  revert i
  decide
theorem case1_join : ∃ z, Reach case1b (exchange case1p 0 1) z ∧ Reach case1b (exchange case1p 0 1) z := by
  have hL0 : Reach case1b (exchange case1p 0 1) (exchange case1p 0 1) := .refl
  have hR0 : Reach case1b (exchange case1p 0 1) (exchange case1p 0 1) := .refl
  have he : (exchange case1p 0 1) = (exchange case1p 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange case1p 0 1),hL0,he ▸ hR0⟩

noncomputable def case2p : Placement 4 := Equiv.ofBijective (![1,0,3,2] : Fin 4 → Fin 4) (by decide)
def case2b : Fin 4 → Nat := ![0,0,0,0]
theorem case2_strongest : case2b = suffixCap (peakCaps case2p 1 2 1 3) := by
  funext i
  revert i
  decide
theorem case2_join : ∃ z, Reach case2b (exchange case2p 0 1) z ∧ Reach case2b (exchange case2p 0 1) z := by
  have hL0 : Reach case2b (exchange case2p 0 1) (exchange case2p 0 1) := .refl
  have hR0 : Reach case2b (exchange case2p 0 1) (exchange case2p 0 1) := .refl
  have he : (exchange case2p 0 1) = (exchange case2p 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange case2p 0 1),hL0,he ▸ hR0⟩

noncomputable def case3p : Placement 4 := Equiv.ofBijective (![1,2,0,3] : Fin 4 → Fin 4) (by decide)
def case3b : Fin 4 → Nat := ![0,0,0,0]
theorem case3_strongest : case3b = suffixCap (peakCaps case3p 2 3 2 3) := by
  funext i
  revert i
  decide
theorem case3_join : ∃ z, Reach case3b (exchange case3p 0 2) z ∧ Reach case3b (exchange case3p 1 2) z := by
  have hL0 : Reach case3b (exchange case3p 0 2) (exchange case3p 0 2) := .refl
  have hL1 : Reach case3b (exchange case3p 0 2) (exchange (exchange case3p 0 2) 1 2) := hL0.tail ⟨by unfold Valid; decide, 1, 2, 3, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case3b (exchange case3p 1 2) (exchange case3p 1 2) := .refl
  have hR1 : Reach case3b (exchange case3p 1 2) (exchange (exchange case3p 1 2) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 2, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case3p 0 2) 1 2) = (exchange (exchange case3p 1 2) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case3p 0 2) 1 2),hL1,he ▸ hR1⟩

noncomputable def case4p : Placement 4 := Equiv.ofBijective (![2,0,1,3] : Fin 4 → Fin 4) (by decide)
def case4b : Fin 4 → Nat := ![0,0,0,0]
theorem case4_strongest : case4b = suffixCap (peakCaps case4p 1 3 2 3) := by
  funext i
  revert i
  decide
theorem case4_join : ∃ z, Reach case4b (exchange case4p 0 1) z ∧ Reach case4b (exchange case4p 0 2) z := by
  have hL0 : Reach case4b (exchange case4p 0 1) (exchange case4p 0 1) := .refl
  have hL1 : Reach case4b (exchange case4p 0 1) (exchange (exchange case4p 0 1) 1 2) := hL0.tail ⟨by unfold Valid; decide, 1, 2, 3, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case4b (exchange case4p 0 2) (exchange case4p 0 2) := .refl
  have hR1 : Reach case4b (exchange case4p 0 2) (exchange (exchange case4p 0 2) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 2, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case4p 0 1) 1 2) = (exchange (exchange case4p 0 2) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case4p 0 1) 1 2),hL1,he ▸ hR1⟩

noncomputable def case5p : Placement 4 := Equiv.ofBijective (![2,1,0,3] : Fin 4 → Fin 4) (by decide)
def case5b : Fin 4 → Nat := ![0,0,0,0]
theorem case5_strongest : case5b = suffixCap (peakCaps case5p 1 3 2 3) := by
  funext i
  revert i
  decide
theorem case5_join : ∃ z, Reach case5b (exchange case5p 0 1) z ∧ Reach case5b (exchange case5p 0 2) z := by
  have hL0 : Reach case5b (exchange case5p 0 1) (exchange case5p 0 1) := .refl
  have hL1 : Reach case5b (exchange case5p 0 1) (exchange (exchange case5p 0 1) 0 2) := hL0.tail ⟨by unfold Valid; decide, 0, 2, 3, by unfold Legal; decide, rfl⟩
  have hL2 : Reach case5b (exchange case5p 0 1) (exchange (exchange (exchange case5p 0 1) 0 2) 1 2) := hL1.tail ⟨by unfold Valid; decide, 1, 2, 3, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case5b (exchange case5p 0 2) (exchange case5p 0 2) := .refl
  have he : (exchange (exchange (exchange case5p 0 1) 0 2) 1 2) = (exchange case5p 0 2) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange (exchange case5p 0 1) 0 2) 1 2),hL2,he ▸ hR0⟩

noncomputable def case6p : Placement 4 := Equiv.ofBijective (![2,1,0,3] : Fin 4 → Fin 4) (by decide)
def case6b : Fin 4 → Nat := ![0,0,0,0]
theorem case6_strongest : case6b = suffixCap (peakCaps case6p 1 3 2 3) := by
  funext i
  revert i
  decide
theorem case6_join : ∃ z, Reach case6b (exchange case6p 0 1) z ∧ Reach case6b (exchange case6p 1 2) z := by
  have hL0 : Reach case6b (exchange case6p 0 1) (exchange case6p 0 1) := .refl
  have hL1 : Reach case6b (exchange case6p 0 1) (exchange (exchange case6p 0 1) 0 2) := hL0.tail ⟨by unfold Valid; decide, 0, 2, 3, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case6b (exchange case6p 1 2) (exchange case6p 1 2) := .refl
  have hR1 : Reach case6b (exchange case6p 1 2) (exchange (exchange case6p 1 2) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 3, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case6p 0 1) 0 2) = (exchange (exchange case6p 1 2) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case6p 0 1) 0 2),hL1,he ▸ hR1⟩

noncomputable def case7p : Placement 4 := Equiv.ofBijective (![2,1,0,3] : Fin 4 → Fin 4) (by decide)
def case7b : Fin 4 → Nat := ![0,0,0,0]
theorem case7_strongest : case7b = suffixCap (peakCaps case7p 2 3 2 3) := by
  funext i
  revert i
  decide
theorem case7_join : ∃ z, Reach case7b (exchange case7p 0 2) z ∧ Reach case7b (exchange case7p 1 2) z := by
  have hL0 : Reach case7b (exchange case7p 0 2) (exchange case7p 0 2) := .refl
  have hR0 : Reach case7b (exchange case7p 1 2) (exchange case7p 1 2) := .refl
  have hR1 : Reach case7b (exchange case7p 1 2) (exchange (exchange case7p 1 2) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 3, by unfold Legal; decide, rfl⟩
  have hR2 : Reach case7b (exchange case7p 1 2) (exchange (exchange (exchange case7p 1 2) 0 1) 1 2) := hR1.tail ⟨by unfold Valid; decide, 1, 2, 3, by unfold Legal; decide, rfl⟩
  have he : (exchange case7p 0 2) = (exchange (exchange (exchange case7p 1 2) 0 1) 1 2) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange case7p 0 2),hL0,he ▸ hR2⟩

noncomputable def case8p : Placement 5 := Equiv.ofBijective (![1,0,3,2,4] : Fin 5 → Fin 5) (by decide)
def case8b : Fin 5 → Nat := ![0,0,0,2,2]
theorem case8_strongest : case8b = suffixCap (peakCaps case8p 1 2 3 4) := by
  funext i
  revert i
  decide
theorem case8_join : ∃ z, Reach case8b (exchange case8p 0 1) z ∧ Reach case8b (exchange case8p 2 3) z := by
  have hL0 : Reach case8b (exchange case8p 0 1) (exchange case8p 0 1) := .refl
  have hL1 : Reach case8b (exchange case8p 0 1) (exchange (exchange case8p 0 1) 2 3) := hL0.tail ⟨by unfold Valid; decide, 2, 3, 4, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case8b (exchange case8p 2 3) (exchange case8p 2 3) := .refl
  have hR1 : Reach case8b (exchange case8p 2 3) (exchange (exchange case8p 2 3) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 2, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case8p 0 1) 2 3) = (exchange (exchange case8p 2 3) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case8p 0 1) 2 3),hL1,he ▸ hR1⟩

noncomputable def case9p : Placement 5 := Equiv.ofBijective (![1,0,3,2,4] : Fin 5 → Fin 5) (by decide)
def case9b : Fin 5 → Nat := ![0,0,0,0,2]
theorem case9_strongest : case9b = suffixCap (peakCaps case9p 1 3 3 4) := by
  funext i
  revert i
  decide
theorem case9_join : ∃ z, Reach case9b (exchange case9p 0 1) z ∧ Reach case9b (exchange case9p 2 3) z := by
  have hL0 : Reach case9b (exchange case9p 0 1) (exchange case9p 0 1) := .refl
  have hL1 : Reach case9b (exchange case9p 0 1) (exchange (exchange case9p 0 1) 2 3) := hL0.tail ⟨by unfold Valid; decide, 2, 3, 4, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case9b (exchange case9p 2 3) (exchange case9p 2 3) := .refl
  have hR1 : Reach case9b (exchange case9p 2 3) (exchange (exchange case9p 2 3) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 2, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case9p 0 1) 2 3) = (exchange (exchange case9p 2 3) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case9p 0 1) 2 3),hL1,he ▸ hR1⟩

noncomputable def case10p : Placement 5 := Equiv.ofBijective (![1,0,3,2,4] : Fin 5 → Fin 5) (by decide)
def case10b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case10_strongest : case10b = suffixCap (peakCaps case10p 1 4 3 4) := by
  funext i
  revert i
  decide
theorem case10_join : ∃ z, Reach case10b (exchange case10p 0 1) z ∧ Reach case10b (exchange case10p 2 3) z := by
  have hL0 : Reach case10b (exchange case10p 0 1) (exchange case10p 0 1) := .refl
  have hL1 : Reach case10b (exchange case10p 0 1) (exchange (exchange case10p 0 1) 2 3) := hL0.tail ⟨by unfold Valid; decide, 2, 3, 4, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case10b (exchange case10p 2 3) (exchange case10p 2 3) := .refl
  have hR1 : Reach case10b (exchange case10p 2 3) (exchange (exchange case10p 2 3) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 2, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case10p 0 1) 2 3) = (exchange (exchange case10p 2 3) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case10p 0 1) 2 3),hL1,he ▸ hR1⟩

noncomputable def case11p : Placement 5 := Equiv.ofBijective (![1,2,0,3,4] : Fin 5 → Fin 5) (by decide)
def case11b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case11_strongest : case11b = suffixCap (peakCaps case11p 2 3 2 4) := by
  funext i
  revert i
  decide
theorem case11_join : ∃ z, Reach case11b (exchange case11p 0 2) z ∧ Reach case11b (exchange case11p 1 2) z := by
  have hL0 : Reach case11b (exchange case11p 0 2) (exchange case11p 0 2) := .refl
  have hL1 : Reach case11b (exchange case11p 0 2) (exchange (exchange case11p 0 2) 1 2) := hL0.tail ⟨by unfold Valid; decide, 1, 2, 3, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case11b (exchange case11p 1 2) (exchange case11p 1 2) := .refl
  have hR1 : Reach case11b (exchange case11p 1 2) (exchange (exchange case11p 1 2) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 2, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case11p 0 2) 1 2) = (exchange (exchange case11p 1 2) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case11p 0 2) 1 2),hL1,he ▸ hR1⟩

noncomputable def case12p : Placement 5 := Equiv.ofBijective (![1,2,0,3,4] : Fin 5 → Fin 5) (by decide)
def case12b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case12_strongest : case12b = suffixCap (peakCaps case12p 2 4 2 3) := by
  funext i
  revert i
  decide
theorem case12_join : ∃ z, Reach case12b (exchange case12p 0 2) z ∧ Reach case12b (exchange case12p 1 2) z := by
  have hL0 : Reach case12b (exchange case12p 0 2) (exchange case12p 0 2) := .refl
  have hL1 : Reach case12b (exchange case12p 0 2) (exchange (exchange case12p 0 2) 1 2) := hL0.tail ⟨by unfold Valid; decide, 1, 2, 3, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case12b (exchange case12p 1 2) (exchange case12p 1 2) := .refl
  have hR1 : Reach case12b (exchange case12p 1 2) (exchange (exchange case12p 1 2) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 2, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case12p 0 2) 1 2) = (exchange (exchange case12p 1 2) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case12p 0 2) 1 2),hL1,he ▸ hR1⟩

noncomputable def case13p : Placement 5 := Equiv.ofBijective (![1,2,0,4,3] : Fin 5 → Fin 5) (by decide)
def case13b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case13_strongest : case13b = suffixCap (peakCaps case13p 2 3 2 4) := by
  funext i
  revert i
  decide
theorem case13_join : ∃ z, Reach case13b (exchange case13p 0 2) z ∧ Reach case13b (exchange case13p 1 2) z := by
  have hL0 : Reach case13b (exchange case13p 0 2) (exchange case13p 0 2) := .refl
  have hL1 : Reach case13b (exchange case13p 0 2) (exchange (exchange case13p 0 2) 1 2) := hL0.tail ⟨by unfold Valid; decide, 1, 2, 3, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case13b (exchange case13p 1 2) (exchange case13p 1 2) := .refl
  have hR1 : Reach case13b (exchange case13p 1 2) (exchange (exchange case13p 1 2) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 2, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case13p 0 2) 1 2) = (exchange (exchange case13p 1 2) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case13p 0 2) 1 2),hL1,he ▸ hR1⟩

noncomputable def case14p : Placement 5 := Equiv.ofBijective (![1,2,0,4,3] : Fin 5 → Fin 5) (by decide)
def case14b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case14_strongest : case14b = suffixCap (peakCaps case14p 2 4 2 3) := by
  funext i
  revert i
  decide
theorem case14_join : ∃ z, Reach case14b (exchange case14p 0 2) z ∧ Reach case14b (exchange case14p 1 2) z := by
  have hL0 : Reach case14b (exchange case14p 0 2) (exchange case14p 0 2) := .refl
  have hL1 : Reach case14b (exchange case14p 0 2) (exchange (exchange case14p 0 2) 1 2) := hL0.tail ⟨by unfold Valid; decide, 1, 2, 3, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case14b (exchange case14p 1 2) (exchange case14p 1 2) := .refl
  have hR1 : Reach case14b (exchange case14p 1 2) (exchange (exchange case14p 1 2) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 2, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case14p 0 2) 1 2) = (exchange (exchange case14p 1 2) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case14p 0 2) 1 2),hL1,he ▸ hR1⟩

noncomputable def case15p : Placement 5 := Equiv.ofBijective (![1,3,0,2,4] : Fin 5 → Fin 5) (by decide)
def case15b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case15_strongest : case15b = suffixCap (peakCaps case15p 2 3 2 4) := by
  funext i
  revert i
  decide
theorem case15_join : ∃ z, Reach case15b (exchange case15p 0 2) z ∧ Reach case15b (exchange case15p 1 2) z := by
  have hL0 : Reach case15b (exchange case15p 0 2) (exchange case15p 0 2) := .refl
  have hL1 : Reach case15b (exchange case15p 0 2) (exchange (exchange case15p 0 2) 1 2) := hL0.tail ⟨by unfold Valid; decide, 1, 2, 4, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case15b (exchange case15p 1 2) (exchange case15p 1 2) := .refl
  have hR1 : Reach case15b (exchange case15p 1 2) (exchange (exchange case15p 1 2) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 2, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case15p 0 2) 1 2) = (exchange (exchange case15p 1 2) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case15p 0 2) 1 2),hL1,he ▸ hR1⟩

noncomputable def case16p : Placement 5 := Equiv.ofBijective (![1,3,0,2,4] : Fin 5 → Fin 5) (by decide)
def case16b : Fin 5 → Nat := ![0,0,0,0,2]
theorem case16_strongest : case16b = suffixCap (peakCaps case16p 2 3 3 4) := by
  funext i
  revert i
  decide
theorem case16_join : ∃ z, Reach case16b (exchange case16p 0 2) z ∧ Reach case16b (exchange case16p 1 3) z := by
  have hL0 : Reach case16b (exchange case16p 0 2) (exchange case16p 0 2) := .refl
  have hL1 : Reach case16b (exchange case16p 0 2) (exchange (exchange case16p 0 2) 1 3) := hL0.tail ⟨by unfold Valid; decide, 1, 3, 4, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case16b (exchange case16p 1 3) (exchange case16p 1 3) := .refl
  have hR1 : Reach case16b (exchange case16p 1 3) (exchange (exchange case16p 1 3) 0 2) := hR0.tail ⟨by unfold Valid; decide, 0, 2, 3, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case16p 0 2) 1 3) = (exchange (exchange case16p 1 3) 0 2) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case16p 0 2) 1 3),hL1,he ▸ hR1⟩

noncomputable def case17p : Placement 5 := Equiv.ofBijective (![1,3,0,2,4] : Fin 5 → Fin 5) (by decide)
def case17b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case17_strongest : case17b = suffixCap (peakCaps case17p 2 4 3 4) := by
  funext i
  revert i
  decide
theorem case17_join : ∃ z, Reach case17b (exchange case17p 0 2) z ∧ Reach case17b (exchange case17p 1 3) z := by
  have hL0 : Reach case17b (exchange case17p 0 2) (exchange case17p 0 2) := .refl
  have hL1 : Reach case17b (exchange case17p 0 2) (exchange (exchange case17p 0 2) 1 3) := hL0.tail ⟨by unfold Valid; decide, 1, 3, 4, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case17b (exchange case17p 1 3) (exchange case17p 1 3) := .refl
  have hR1 : Reach case17b (exchange case17p 1 3) (exchange (exchange case17p 1 3) 0 2) := hR0.tail ⟨by unfold Valid; decide, 0, 2, 3, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case17p 0 2) 1 3) = (exchange (exchange case17p 1 3) 0 2) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case17p 0 2) 1 3),hL1,he ▸ hR1⟩

noncomputable def case18p : Placement 5 := Equiv.ofBijective (![1,3,0,4,2] : Fin 5 → Fin 5) (by decide)
def case18b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case18_strongest : case18b = suffixCap (peakCaps case18p 2 4 2 3) := by
  funext i
  revert i
  decide
theorem case18_join : ∃ z, Reach case18b (exchange case18p 0 2) z ∧ Reach case18b (exchange case18p 1 2) z := by
  have hL0 : Reach case18b (exchange case18p 0 2) (exchange case18p 0 2) := .refl
  have hL1 : Reach case18b (exchange case18p 0 2) (exchange (exchange case18p 0 2) 1 2) := hL0.tail ⟨by unfold Valid; decide, 1, 2, 3, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case18b (exchange case18p 1 2) (exchange case18p 1 2) := .refl
  have hR1 : Reach case18b (exchange case18p 1 2) (exchange (exchange case18p 1 2) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 2, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case18p 0 2) 1 2) = (exchange (exchange case18p 1 2) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case18p 0 2) 1 2),hL1,he ▸ hR1⟩

noncomputable def case19p : Placement 5 := Equiv.ofBijective (![1,3,2,0,4] : Fin 5 → Fin 5) (by decide)
def case19b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case19_strongest : case19b = suffixCap (peakCaps case19p 3 4 2 4) := by
  funext i
  revert i
  decide
theorem case19_join : ∃ z, Reach case19b (exchange case19p 0 3) z ∧ Reach case19b (exchange case19p 1 2) z := by
  have hL0 : Reach case19b (exchange case19p 0 3) (exchange case19p 0 3) := .refl
  have hL1 : Reach case19b (exchange case19p 0 3) (exchange (exchange case19p 0 3) 1 2) := hL0.tail ⟨by unfold Valid; decide, 1, 2, 4, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case19b (exchange case19p 1 2) (exchange case19p 1 2) := .refl
  have hR1 : Reach case19b (exchange case19p 1 2) (exchange (exchange case19p 1 2) 0 3) := hR0.tail ⟨by unfold Valid; decide, 0, 3, 4, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case19p 0 3) 1 2) = (exchange (exchange case19p 1 2) 0 3) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case19p 0 3) 1 2),hL1,he ▸ hR1⟩

noncomputable def case20p : Placement 5 := Equiv.ofBijective (![2,0,1,3,4] : Fin 5 → Fin 5) (by decide)
def case20b : Fin 5 → Nat := ![0,0,0,0,1]
theorem case20_strongest : case20b = suffixCap (peakCaps case20p 1 3 2 4) := by
  funext i
  revert i
  decide
theorem case20_join : ∃ z, Reach case20b (exchange case20p 0 1) z ∧ Reach case20b (exchange case20p 0 2) z := by
  have hL0 : Reach case20b (exchange case20p 0 1) (exchange case20p 0 1) := .refl
  have hL1 : Reach case20b (exchange case20p 0 1) (exchange (exchange case20p 0 1) 1 2) := hL0.tail ⟨by unfold Valid; decide, 1, 2, 3, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case20b (exchange case20p 0 2) (exchange case20p 0 2) := .refl
  have hR1 : Reach case20b (exchange case20p 0 2) (exchange (exchange case20p 0 2) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 2, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case20p 0 1) 1 2) = (exchange (exchange case20p 0 2) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case20p 0 1) 1 2),hL1,he ▸ hR1⟩

noncomputable def case21p : Placement 5 := Equiv.ofBijective (![2,0,1,3,4] : Fin 5 → Fin 5) (by decide)
def case21b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case21_strongest : case21b = suffixCap (peakCaps case21p 1 4 2 3) := by
  funext i
  revert i
  decide
theorem case21_join : ∃ z, Reach case21b (exchange case21p 0 1) z ∧ Reach case21b (exchange case21p 0 2) z := by
  have hL0 : Reach case21b (exchange case21p 0 1) (exchange case21p 0 1) := .refl
  have hL1 : Reach case21b (exchange case21p 0 1) (exchange (exchange case21p 0 1) 1 2) := hL0.tail ⟨by unfold Valid; decide, 1, 2, 3, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case21b (exchange case21p 0 2) (exchange case21p 0 2) := .refl
  have hR1 : Reach case21b (exchange case21p 0 2) (exchange (exchange case21p 0 2) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 2, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case21p 0 1) 1 2) = (exchange (exchange case21p 0 2) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case21p 0 1) 1 2),hL1,he ▸ hR1⟩

noncomputable def case22p : Placement 5 := Equiv.ofBijective (![2,0,1,4,3] : Fin 5 → Fin 5) (by decide)
def case22b : Fin 5 → Nat := ![0,0,0,0,1]
theorem case22_strongest : case22b = suffixCap (peakCaps case22p 1 3 2 4) := by
  funext i
  revert i
  decide
theorem case22_join : ∃ z, Reach case22b (exchange case22p 0 1) z ∧ Reach case22b (exchange case22p 0 2) z := by
  have hL0 : Reach case22b (exchange case22p 0 1) (exchange case22p 0 1) := .refl
  have hL1 : Reach case22b (exchange case22p 0 1) (exchange (exchange case22p 0 1) 1 2) := hL0.tail ⟨by unfold Valid; decide, 1, 2, 3, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case22b (exchange case22p 0 2) (exchange case22p 0 2) := .refl
  have hR1 : Reach case22b (exchange case22p 0 2) (exchange (exchange case22p 0 2) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 2, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case22p 0 1) 1 2) = (exchange (exchange case22p 0 2) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case22p 0 1) 1 2),hL1,he ▸ hR1⟩

noncomputable def case23p : Placement 5 := Equiv.ofBijective (![2,0,1,4,3] : Fin 5 → Fin 5) (by decide)
def case23b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case23_strongest : case23b = suffixCap (peakCaps case23p 1 4 2 3) := by
  funext i
  revert i
  decide
theorem case23_join : ∃ z, Reach case23b (exchange case23p 0 1) z ∧ Reach case23b (exchange case23p 0 2) z := by
  have hL0 : Reach case23b (exchange case23p 0 1) (exchange case23p 0 1) := .refl
  have hL1 : Reach case23b (exchange case23p 0 1) (exchange (exchange case23p 0 1) 1 2) := hL0.tail ⟨by unfold Valid; decide, 1, 2, 3, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case23b (exchange case23p 0 2) (exchange case23p 0 2) := .refl
  have hR1 : Reach case23b (exchange case23p 0 2) (exchange (exchange case23p 0 2) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 2, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case23p 0 1) 1 2) = (exchange (exchange case23p 0 2) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case23p 0 1) 1 2),hL1,he ▸ hR1⟩

noncomputable def case24p : Placement 5 := Equiv.ofBijective (![2,0,3,1,4] : Fin 5 → Fin 5) (by decide)
def case24b : Fin 5 → Nat := ![0,0,0,1,1]
theorem case24_strongest : case24b = suffixCap (peakCaps case24p 1 2 3 4) := by
  funext i
  revert i
  decide
theorem case24_join : ∃ z, Reach case24b (exchange case24p 0 1) z ∧ Reach case24b (exchange case24p 0 3) z := by
  have hL0 : Reach case24b (exchange case24p 0 1) (exchange case24p 0 1) := .refl
  have hL1 : Reach case24b (exchange case24p 0 1) (exchange (exchange case24p 0 1) 1 3) := hL0.tail ⟨by unfold Valid; decide, 1, 3, 4, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case24b (exchange case24p 0 3) (exchange case24p 0 3) := .refl
  have hR1 : Reach case24b (exchange case24p 0 3) (exchange (exchange case24p 0 3) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 2, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case24p 0 1) 1 3) = (exchange (exchange case24p 0 3) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case24p 0 1) 1 3),hL1,he ▸ hR1⟩

noncomputable def case25p : Placement 5 := Equiv.ofBijective (![2,0,3,1,4] : Fin 5 → Fin 5) (by decide)
def case25b : Fin 5 → Nat := ![0,0,0,1,1]
theorem case25_strongest : case25b = suffixCap (peakCaps case25p 1 2 3 4) := by
  funext i
  revert i
  decide
theorem case25_join : ∃ z, Reach case25b (exchange case25p 0 1) z ∧ Reach case25b (exchange case25p 2 3) z := by
  have hL0 : Reach case25b (exchange case25p 0 1) (exchange case25p 0 1) := .refl
  have hL1 : Reach case25b (exchange case25p 0 1) (exchange (exchange case25p 0 1) 1 3) := hL0.tail ⟨by unfold Valid; decide, 1, 3, 4, by unfold Legal; decide, rfl⟩
  have hL2 : Reach case25b (exchange case25p 0 1) (exchange (exchange (exchange case25p 0 1) 1 3) 2 3) := hL1.tail ⟨by unfold Valid; decide, 2, 3, 4, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case25b (exchange case25p 2 3) (exchange case25p 2 3) := .refl
  have hR1 : Reach case25b (exchange case25p 2 3) (exchange (exchange case25p 2 3) 0 2) := hR0.tail ⟨by unfold Valid; decide, 0, 2, 3, by unfold Legal; decide, rfl⟩
  have hR2 : Reach case25b (exchange case25p 2 3) (exchange (exchange (exchange case25p 2 3) 0 2) 0 1) := hR1.tail ⟨by unfold Valid; decide, 0, 1, 2, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange (exchange case25p 0 1) 1 3) 2 3) = (exchange (exchange (exchange case25p 2 3) 0 2) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange (exchange case25p 0 1) 1 3) 2 3),hL2,he ▸ hR2⟩

noncomputable def case26p : Placement 5 := Equiv.ofBijective (![2,0,3,1,4] : Fin 5 → Fin 5) (by decide)
def case26b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case26_strongest : case26b = suffixCap (peakCaps case26p 1 4 3 4) := by
  funext i
  revert i
  decide
theorem case26_join : ∃ z, Reach case26b (exchange case26p 0 1) z ∧ Reach case26b (exchange case26p 2 3) z := by
  have hL0 : Reach case26b (exchange case26p 0 1) (exchange case26p 0 1) := .refl
  have hL1 : Reach case26b (exchange case26p 0 1) (exchange (exchange case26p 0 1) 2 3) := hL0.tail ⟨by unfold Valid; decide, 2, 3, 4, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case26b (exchange case26p 2 3) (exchange case26p 2 3) := .refl
  have hR1 : Reach case26b (exchange case26p 2 3) (exchange (exchange case26p 2 3) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 3, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case26p 0 1) 2 3) = (exchange (exchange case26p 2 3) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case26p 0 1) 2 3),hL1,he ▸ hR1⟩

noncomputable def case27p : Placement 5 := Equiv.ofBijective (![2,0,4,1,3] : Fin 5 → Fin 5) (by decide)
def case27b : Fin 5 → Nat := ![0,0,0,1,1]
theorem case27_strongest : case27b = suffixCap (peakCaps case27p 1 2 3 4) := by
  funext i
  revert i
  decide
theorem case27_join : ∃ z, Reach case27b (exchange case27p 0 1) z ∧ Reach case27b (exchange case27p 0 3) z := by
  have hL0 : Reach case27b (exchange case27p 0 1) (exchange case27p 0 1) := .refl
  have hL1 : Reach case27b (exchange case27p 0 1) (exchange (exchange case27p 0 1) 1 3) := hL0.tail ⟨by unfold Valid; decide, 1, 3, 4, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case27b (exchange case27p 0 3) (exchange case27p 0 3) := .refl
  have hR1 : Reach case27b (exchange case27p 0 3) (exchange (exchange case27p 0 3) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 2, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case27p 0 1) 1 3) = (exchange (exchange case27p 0 3) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case27p 0 1) 1 3),hL1,he ▸ hR1⟩

noncomputable def case28p : Placement 5 := Equiv.ofBijective (![2,1,0,3,4] : Fin 5 → Fin 5) (by decide)
def case28b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case28_strongest : case28b = suffixCap (peakCaps case28p 1 3 2 4) := by
  funext i
  revert i
  decide
theorem case28_join : ∃ z, Reach case28b (exchange case28p 0 1) z ∧ Reach case28b (exchange case28p 0 2) z := by
  have hL0 : Reach case28b (exchange case28p 0 1) (exchange case28p 0 1) := .refl
  have hL1 : Reach case28b (exchange case28p 0 1) (exchange (exchange case28p 0 1) 0 2) := hL0.tail ⟨by unfold Valid; decide, 0, 2, 3, by unfold Legal; decide, rfl⟩
  have hL2 : Reach case28b (exchange case28p 0 1) (exchange (exchange (exchange case28p 0 1) 0 2) 1 2) := hL1.tail ⟨by unfold Valid; decide, 1, 2, 3, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case28b (exchange case28p 0 2) (exchange case28p 0 2) := .refl
  have he : (exchange (exchange (exchange case28p 0 1) 0 2) 1 2) = (exchange case28p 0 2) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange (exchange case28p 0 1) 0 2) 1 2),hL2,he ▸ hR0⟩

noncomputable def case29p : Placement 5 := Equiv.ofBijective (![2,1,0,3,4] : Fin 5 → Fin 5) (by decide)
def case29b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case29_strongest : case29b = suffixCap (peakCaps case29p 1 3 2 4) := by
  funext i
  revert i
  decide
theorem case29_join : ∃ z, Reach case29b (exchange case29p 0 1) z ∧ Reach case29b (exchange case29p 1 2) z := by
  have hL0 : Reach case29b (exchange case29p 0 1) (exchange case29p 0 1) := .refl
  have hL1 : Reach case29b (exchange case29p 0 1) (exchange (exchange case29p 0 1) 0 2) := hL0.tail ⟨by unfold Valid; decide, 0, 2, 3, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case29b (exchange case29p 1 2) (exchange case29p 1 2) := .refl
  have hR1 : Reach case29b (exchange case29p 1 2) (exchange (exchange case29p 1 2) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 3, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case29p 0 1) 0 2) = (exchange (exchange case29p 1 2) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case29p 0 1) 0 2),hL1,he ▸ hR1⟩

noncomputable def case30p : Placement 5 := Equiv.ofBijective (![2,1,0,3,4] : Fin 5 → Fin 5) (by decide)
def case30b : Fin 5 → Nat := ![0,0,0,0,1]
theorem case30_strongest : case30b = suffixCap (peakCaps case30p 1 4 2 3) := by
  funext i
  revert i
  decide
theorem case30_join : ∃ z, Reach case30b (exchange case30p 0 1) z ∧ Reach case30b (exchange case30p 0 2) z := by
  have hL0 : Reach case30b (exchange case30p 0 1) (exchange case30p 0 1) := .refl
  have hL1 : Reach case30b (exchange case30p 0 1) (exchange (exchange case30p 0 1) 0 2) := hL0.tail ⟨by unfold Valid; decide, 0, 2, 3, by unfold Legal; decide, rfl⟩
  have hL2 : Reach case30b (exchange case30p 0 1) (exchange (exchange (exchange case30p 0 1) 0 2) 1 2) := hL1.tail ⟨by unfold Valid; decide, 1, 2, 3, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case30b (exchange case30p 0 2) (exchange case30p 0 2) := .refl
  have he : (exchange (exchange (exchange case30p 0 1) 0 2) 1 2) = (exchange case30p 0 2) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange (exchange case30p 0 1) 0 2) 1 2),hL2,he ▸ hR0⟩

noncomputable def case31p : Placement 5 := Equiv.ofBijective (![2,1,0,3,4] : Fin 5 → Fin 5) (by decide)
def case31b : Fin 5 → Nat := ![0,0,0,0,1]
theorem case31_strongest : case31b = suffixCap (peakCaps case31p 1 4 2 3) := by
  funext i
  revert i
  decide
theorem case31_join : ∃ z, Reach case31b (exchange case31p 0 1) z ∧ Reach case31b (exchange case31p 1 2) z := by
  have hL0 : Reach case31b (exchange case31p 0 1) (exchange case31p 0 1) := .refl
  have hL1 : Reach case31b (exchange case31p 0 1) (exchange (exchange case31p 0 1) 0 2) := hL0.tail ⟨by unfold Valid; decide, 0, 2, 3, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case31b (exchange case31p 1 2) (exchange case31p 1 2) := .refl
  have hR1 : Reach case31b (exchange case31p 1 2) (exchange (exchange case31p 1 2) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 3, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case31p 0 1) 0 2) = (exchange (exchange case31p 1 2) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case31p 0 1) 0 2),hL1,he ▸ hR1⟩

noncomputable def case32p : Placement 5 := Equiv.ofBijective (![2,1,0,3,4] : Fin 5 → Fin 5) (by decide)
def case32b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case32_strongest : case32b = suffixCap (peakCaps case32p 2 3 2 4) := by
  funext i
  revert i
  decide
theorem case32_join : ∃ z, Reach case32b (exchange case32p 0 2) z ∧ Reach case32b (exchange case32p 1 2) z := by
  have hL0 : Reach case32b (exchange case32p 0 2) (exchange case32p 0 2) := .refl
  have hR0 : Reach case32b (exchange case32p 1 2) (exchange case32p 1 2) := .refl
  have hR1 : Reach case32b (exchange case32p 1 2) (exchange (exchange case32p 1 2) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 3, by unfold Legal; decide, rfl⟩
  have hR2 : Reach case32b (exchange case32p 1 2) (exchange (exchange (exchange case32p 1 2) 0 1) 1 2) := hR1.tail ⟨by unfold Valid; decide, 1, 2, 3, by unfold Legal; decide, rfl⟩
  have he : (exchange case32p 0 2) = (exchange (exchange (exchange case32p 1 2) 0 1) 1 2) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange case32p 0 2),hL0,he ▸ hR2⟩

noncomputable def case33p : Placement 5 := Equiv.ofBijective (![2,1,0,3,4] : Fin 5 → Fin 5) (by decide)
def case33b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case33_strongest : case33b = suffixCap (peakCaps case33p 2 4 2 3) := by
  funext i
  revert i
  decide
theorem case33_join : ∃ z, Reach case33b (exchange case33p 0 2) z ∧ Reach case33b (exchange case33p 1 2) z := by
  have hL0 : Reach case33b (exchange case33p 0 2) (exchange case33p 0 2) := .refl
  have hR0 : Reach case33b (exchange case33p 1 2) (exchange case33p 1 2) := .refl
  have hR1 : Reach case33b (exchange case33p 1 2) (exchange (exchange case33p 1 2) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 3, by unfold Legal; decide, rfl⟩
  have hR2 : Reach case33b (exchange case33p 1 2) (exchange (exchange (exchange case33p 1 2) 0 1) 1 2) := hR1.tail ⟨by unfold Valid; decide, 1, 2, 3, by unfold Legal; decide, rfl⟩
  have he : (exchange case33p 0 2) = (exchange (exchange (exchange case33p 1 2) 0 1) 1 2) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange case33p 0 2),hL0,he ▸ hR2⟩

noncomputable def case34p : Placement 5 := Equiv.ofBijective (![2,1,0,4,3] : Fin 5 → Fin 5) (by decide)
def case34b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case34_strongest : case34b = suffixCap (peakCaps case34p 1 3 2 4) := by
  funext i
  revert i
  decide
theorem case34_join : ∃ z, Reach case34b (exchange case34p 0 1) z ∧ Reach case34b (exchange case34p 0 2) z := by
  have hL0 : Reach case34b (exchange case34p 0 1) (exchange case34p 0 1) := .refl
  have hL1 : Reach case34b (exchange case34p 0 1) (exchange (exchange case34p 0 1) 0 2) := hL0.tail ⟨by unfold Valid; decide, 0, 2, 3, by unfold Legal; decide, rfl⟩
  have hL2 : Reach case34b (exchange case34p 0 1) (exchange (exchange (exchange case34p 0 1) 0 2) 1 2) := hL1.tail ⟨by unfold Valid; decide, 1, 2, 3, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case34b (exchange case34p 0 2) (exchange case34p 0 2) := .refl
  have he : (exchange (exchange (exchange case34p 0 1) 0 2) 1 2) = (exchange case34p 0 2) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange (exchange case34p 0 1) 0 2) 1 2),hL2,he ▸ hR0⟩

noncomputable def case35p : Placement 5 := Equiv.ofBijective (![2,1,0,4,3] : Fin 5 → Fin 5) (by decide)
def case35b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case35_strongest : case35b = suffixCap (peakCaps case35p 1 3 2 4) := by
  funext i
  revert i
  decide
theorem case35_join : ∃ z, Reach case35b (exchange case35p 0 1) z ∧ Reach case35b (exchange case35p 1 2) z := by
  have hL0 : Reach case35b (exchange case35p 0 1) (exchange case35p 0 1) := .refl
  have hL1 : Reach case35b (exchange case35p 0 1) (exchange (exchange case35p 0 1) 0 2) := hL0.tail ⟨by unfold Valid; decide, 0, 2, 3, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case35b (exchange case35p 1 2) (exchange case35p 1 2) := .refl
  have hR1 : Reach case35b (exchange case35p 1 2) (exchange (exchange case35p 1 2) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 3, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case35p 0 1) 0 2) = (exchange (exchange case35p 1 2) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case35p 0 1) 0 2),hL1,he ▸ hR1⟩

noncomputable def case36p : Placement 5 := Equiv.ofBijective (![2,1,0,4,3] : Fin 5 → Fin 5) (by decide)
def case36b : Fin 5 → Nat := ![0,0,0,0,1]
theorem case36_strongest : case36b = suffixCap (peakCaps case36p 1 4 2 3) := by
  funext i
  revert i
  decide
theorem case36_join : ∃ z, Reach case36b (exchange case36p 0 1) z ∧ Reach case36b (exchange case36p 0 2) z := by
  have hL0 : Reach case36b (exchange case36p 0 1) (exchange case36p 0 1) := .refl
  have hL1 : Reach case36b (exchange case36p 0 1) (exchange (exchange case36p 0 1) 0 2) := hL0.tail ⟨by unfold Valid; decide, 0, 2, 3, by unfold Legal; decide, rfl⟩
  have hL2 : Reach case36b (exchange case36p 0 1) (exchange (exchange (exchange case36p 0 1) 0 2) 1 2) := hL1.tail ⟨by unfold Valid; decide, 1, 2, 3, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case36b (exchange case36p 0 2) (exchange case36p 0 2) := .refl
  have he : (exchange (exchange (exchange case36p 0 1) 0 2) 1 2) = (exchange case36p 0 2) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange (exchange case36p 0 1) 0 2) 1 2),hL2,he ▸ hR0⟩

noncomputable def case37p : Placement 5 := Equiv.ofBijective (![2,1,0,4,3] : Fin 5 → Fin 5) (by decide)
def case37b : Fin 5 → Nat := ![0,0,0,0,1]
theorem case37_strongest : case37b = suffixCap (peakCaps case37p 1 4 2 3) := by
  funext i
  revert i
  decide
theorem case37_join : ∃ z, Reach case37b (exchange case37p 0 1) z ∧ Reach case37b (exchange case37p 1 2) z := by
  have hL0 : Reach case37b (exchange case37p 0 1) (exchange case37p 0 1) := .refl
  have hL1 : Reach case37b (exchange case37p 0 1) (exchange (exchange case37p 0 1) 0 2) := hL0.tail ⟨by unfold Valid; decide, 0, 2, 3, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case37b (exchange case37p 1 2) (exchange case37p 1 2) := .refl
  have hR1 : Reach case37b (exchange case37p 1 2) (exchange (exchange case37p 1 2) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 3, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case37p 0 1) 0 2) = (exchange (exchange case37p 1 2) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case37p 0 1) 0 2),hL1,he ▸ hR1⟩

noncomputable def case38p : Placement 5 := Equiv.ofBijective (![2,1,0,4,3] : Fin 5 → Fin 5) (by decide)
def case38b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case38_strongest : case38b = suffixCap (peakCaps case38p 2 3 2 4) := by
  funext i
  revert i
  decide
theorem case38_join : ∃ z, Reach case38b (exchange case38p 0 2) z ∧ Reach case38b (exchange case38p 1 2) z := by
  have hL0 : Reach case38b (exchange case38p 0 2) (exchange case38p 0 2) := .refl
  have hR0 : Reach case38b (exchange case38p 1 2) (exchange case38p 1 2) := .refl
  have hR1 : Reach case38b (exchange case38p 1 2) (exchange (exchange case38p 1 2) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 3, by unfold Legal; decide, rfl⟩
  have hR2 : Reach case38b (exchange case38p 1 2) (exchange (exchange (exchange case38p 1 2) 0 1) 1 2) := hR1.tail ⟨by unfold Valid; decide, 1, 2, 3, by unfold Legal; decide, rfl⟩
  have he : (exchange case38p 0 2) = (exchange (exchange (exchange case38p 1 2) 0 1) 1 2) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange case38p 0 2),hL0,he ▸ hR2⟩

noncomputable def case39p : Placement 5 := Equiv.ofBijective (![2,1,0,4,3] : Fin 5 → Fin 5) (by decide)
def case39b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case39_strongest : case39b = suffixCap (peakCaps case39p 2 4 2 3) := by
  funext i
  revert i
  decide
theorem case39_join : ∃ z, Reach case39b (exchange case39p 0 2) z ∧ Reach case39b (exchange case39p 1 2) z := by
  have hL0 : Reach case39b (exchange case39p 0 2) (exchange case39p 0 2) := .refl
  have hR0 : Reach case39b (exchange case39p 1 2) (exchange case39p 1 2) := .refl
  have hR1 : Reach case39b (exchange case39p 1 2) (exchange (exchange case39p 1 2) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 3, by unfold Legal; decide, rfl⟩
  have hR2 : Reach case39b (exchange case39p 1 2) (exchange (exchange (exchange case39p 1 2) 0 1) 1 2) := hR1.tail ⟨by unfold Valid; decide, 1, 2, 3, by unfold Legal; decide, rfl⟩
  have he : (exchange case39p 0 2) = (exchange (exchange (exchange case39p 1 2) 0 1) 1 2) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange case39p 0 2),hL0,he ▸ hR2⟩

noncomputable def case40p : Placement 5 := Equiv.ofBijective (![2,1,3,0,4] : Fin 5 → Fin 5) (by decide)
def case40b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case40_strongest : case40b = suffixCap (peakCaps case40p 1 2 3 4) := by
  funext i
  revert i
  decide
theorem case40_join : ∃ z, Reach case40b (exchange case40p 0 1) z ∧ Reach case40b (exchange case40p 0 3) z := by
  have hL0 : Reach case40b (exchange case40p 0 1) (exchange case40p 0 1) := .refl
  have hL1 : Reach case40b (exchange case40p 0 1) (exchange (exchange case40p 0 1) 0 3) := hL0.tail ⟨by unfold Valid; decide, 0, 3, 4, by unfold Legal; decide, rfl⟩
  have hL2 : Reach case40b (exchange case40p 0 1) (exchange (exchange (exchange case40p 0 1) 0 3) 1 3) := hL1.tail ⟨by unfold Valid; decide, 1, 3, 4, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case40b (exchange case40p 0 3) (exchange case40p 0 3) := .refl
  have he : (exchange (exchange (exchange case40p 0 1) 0 3) 1 3) = (exchange case40p 0 3) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange (exchange case40p 0 1) 0 3) 1 3),hL2,he ▸ hR0⟩

noncomputable def case41p : Placement 5 := Equiv.ofBijective (![2,1,3,0,4] : Fin 5 → Fin 5) (by decide)
def case41b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case41_strongest : case41b = suffixCap (peakCaps case41p 1 2 3 4) := by
  funext i
  revert i
  decide
theorem case41_join : ∃ z, Reach case41b (exchange case41p 0 1) z ∧ Reach case41b (exchange case41p 1 3) z := by
  have hL0 : Reach case41b (exchange case41p 0 1) (exchange case41p 0 1) := .refl
  have hL1 : Reach case41b (exchange case41p 0 1) (exchange (exchange case41p 0 1) 0 3) := hL0.tail ⟨by unfold Valid; decide, 0, 3, 4, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case41b (exchange case41p 1 3) (exchange case41p 1 3) := .refl
  have hR1 : Reach case41b (exchange case41p 1 3) (exchange (exchange case41p 1 3) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 2, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case41p 0 1) 0 3) = (exchange (exchange case41p 1 3) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case41p 0 1) 0 3),hL1,he ▸ hR1⟩

noncomputable def case42p : Placement 5 := Equiv.ofBijective (![2,1,3,0,4] : Fin 5 → Fin 5) (by decide)
def case42b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case42_strongest : case42b = suffixCap (peakCaps case42p 1 2 3 4) := by
  funext i
  revert i
  decide
theorem case42_join : ∃ z, Reach case42b (exchange case42p 0 1) z ∧ Reach case42b (exchange case42p 2 3) z := by
  have hL0 : Reach case42b (exchange case42p 0 1) (exchange case42p 0 1) := .refl
  have hL1 : Reach case42b (exchange case42p 0 1) (exchange (exchange case42p 0 1) 2 3) := hL0.tail ⟨by unfold Valid; decide, 2, 3, 4, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case42b (exchange case42p 2 3) (exchange case42p 2 3) := .refl
  have hR1 : Reach case42b (exchange case42p 2 3) (exchange (exchange case42p 2 3) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 3, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case42p 0 1) 2 3) = (exchange (exchange case42p 2 3) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case42p 0 1) 2 3),hL1,he ▸ hR1⟩

noncomputable def case43p : Placement 5 := Equiv.ofBijective (![2,1,3,0,4] : Fin 5 → Fin 5) (by decide)
def case43b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case43_strongest : case43b = suffixCap (peakCaps case43p 1 4 3 4) := by
  funext i
  revert i
  decide
theorem case43_join : ∃ z, Reach case43b (exchange case43p 0 1) z ∧ Reach case43b (exchange case43p 2 3) z := by
  have hL0 : Reach case43b (exchange case43p 0 1) (exchange case43p 0 1) := .refl
  have hL1 : Reach case43b (exchange case43p 0 1) (exchange (exchange case43p 0 1) 2 3) := hL0.tail ⟨by unfold Valid; decide, 2, 3, 4, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case43b (exchange case43p 2 3) (exchange case43p 2 3) := .refl
  have hR1 : Reach case43b (exchange case43p 2 3) (exchange (exchange case43p 2 3) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 3, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case43p 0 1) 2 3) = (exchange (exchange case43p 2 3) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case43p 0 1) 2 3),hL1,he ▸ hR1⟩

noncomputable def case44p : Placement 5 := Equiv.ofBijective (![2,1,4,0,3] : Fin 5 → Fin 5) (by decide)
def case44b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case44_strongest : case44b = suffixCap (peakCaps case44p 1 2 3 4) := by
  funext i
  revert i
  decide
theorem case44_join : ∃ z, Reach case44b (exchange case44p 0 1) z ∧ Reach case44b (exchange case44p 0 3) z := by
  have hL0 : Reach case44b (exchange case44p 0 1) (exchange case44p 0 1) := .refl
  have hL1 : Reach case44b (exchange case44p 0 1) (exchange (exchange case44p 0 1) 0 3) := hL0.tail ⟨by unfold Valid; decide, 0, 3, 4, by unfold Legal; decide, rfl⟩
  have hL2 : Reach case44b (exchange case44p 0 1) (exchange (exchange (exchange case44p 0 1) 0 3) 1 3) := hL1.tail ⟨by unfold Valid; decide, 1, 3, 4, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case44b (exchange case44p 0 3) (exchange case44p 0 3) := .refl
  have he : (exchange (exchange (exchange case44p 0 1) 0 3) 1 3) = (exchange case44p 0 3) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange (exchange case44p 0 1) 0 3) 1 3),hL2,he ▸ hR0⟩

noncomputable def case45p : Placement 5 := Equiv.ofBijective (![2,1,4,0,3] : Fin 5 → Fin 5) (by decide)
def case45b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case45_strongest : case45b = suffixCap (peakCaps case45p 1 2 3 4) := by
  funext i
  revert i
  decide
theorem case45_join : ∃ z, Reach case45b (exchange case45p 0 1) z ∧ Reach case45b (exchange case45p 1 3) z := by
  have hL0 : Reach case45b (exchange case45p 0 1) (exchange case45p 0 1) := .refl
  have hL1 : Reach case45b (exchange case45p 0 1) (exchange (exchange case45p 0 1) 0 3) := hL0.tail ⟨by unfold Valid; decide, 0, 3, 4, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case45b (exchange case45p 1 3) (exchange case45p 1 3) := .refl
  have hR1 : Reach case45b (exchange case45p 1 3) (exchange (exchange case45p 1 3) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 2, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case45p 0 1) 0 3) = (exchange (exchange case45p 1 3) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case45p 0 1) 0 3),hL1,he ▸ hR1⟩

noncomputable def case46p : Placement 5 := Equiv.ofBijective (![2,3,0,1,4] : Fin 5 → Fin 5) (by decide)
def case46b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case46_strongest : case46b = suffixCap (peakCaps case46p 2 4 3 4) := by
  funext i
  revert i
  decide
theorem case46_join : ∃ z, Reach case46b (exchange case46p 0 2) z ∧ Reach case46b (exchange case46p 1 3) z := by
  have hL0 : Reach case46b (exchange case46p 0 2) (exchange case46p 0 2) := .refl
  have hL1 : Reach case46b (exchange case46p 0 2) (exchange (exchange case46p 0 2) 1 3) := hL0.tail ⟨by unfold Valid; decide, 1, 3, 4, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case46b (exchange case46p 1 3) (exchange case46p 1 3) := .refl
  have hR1 : Reach case46b (exchange case46p 1 3) (exchange (exchange case46p 1 3) 0 2) := hR0.tail ⟨by unfold Valid; decide, 0, 2, 3, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case46p 0 2) 1 3) = (exchange (exchange case46p 1 3) 0 2) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case46p 0 2) 1 3),hL1,he ▸ hR1⟩

noncomputable def case47p : Placement 5 := Equiv.ofBijective (![2,3,0,1,4] : Fin 5 → Fin 5) (by decide)
def case47b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case47_strongest : case47b = suffixCap (peakCaps case47p 3 4 2 4) := by
  funext i
  revert i
  decide
theorem case47_join : ∃ z, Reach case47b (exchange case47p 0 3) z ∧ Reach case47b (exchange case47p 1 2) z := by
  have hL0 : Reach case47b (exchange case47p 0 3) (exchange case47p 0 3) := .refl
  have hL1 : Reach case47b (exchange case47p 0 3) (exchange (exchange case47p 0 3) 1 2) := hL0.tail ⟨by unfold Valid; decide, 1, 2, 4, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case47b (exchange case47p 1 2) (exchange case47p 1 2) := .refl
  have hR1 : Reach case47b (exchange case47p 1 2) (exchange (exchange case47p 1 2) 0 3) := hR0.tail ⟨by unfold Valid; decide, 0, 3, 4, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case47p 0 3) 1 2) = (exchange (exchange case47p 1 2) 0 3) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case47p 0 3) 1 2),hL1,he ▸ hR1⟩

noncomputable def case48p : Placement 5 := Equiv.ofBijective (![2,3,1,0,4] : Fin 5 → Fin 5) (by decide)
def case48b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case48_strongest : case48b = suffixCap (peakCaps case48p 2 4 3 4) := by
  funext i
  revert i
  decide
theorem case48_join : ∃ z, Reach case48b (exchange case48p 0 2) z ∧ Reach case48b (exchange case48p 1 3) z := by
  have hL0 : Reach case48b (exchange case48p 0 2) (exchange case48p 0 2) := .refl
  have hL1 : Reach case48b (exchange case48p 0 2) (exchange (exchange case48p 0 2) 1 3) := hL0.tail ⟨by unfold Valid; decide, 1, 3, 4, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case48b (exchange case48p 1 3) (exchange case48p 1 3) := .refl
  have hR1 : Reach case48b (exchange case48p 1 3) (exchange (exchange case48p 1 3) 0 2) := hR0.tail ⟨by unfold Valid; decide, 0, 2, 3, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case48p 0 2) 1 3) = (exchange (exchange case48p 1 3) 0 2) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case48p 0 2) 1 3),hL1,he ▸ hR1⟩

noncomputable def case49p : Placement 5 := Equiv.ofBijective (![2,3,1,0,4] : Fin 5 → Fin 5) (by decide)
def case49b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case49_strongest : case49b = suffixCap (peakCaps case49p 3 4 2 4) := by
  funext i
  revert i
  decide
theorem case49_join : ∃ z, Reach case49b (exchange case49p 0 3) z ∧ Reach case49b (exchange case49p 1 2) z := by
  have hL0 : Reach case49b (exchange case49p 0 3) (exchange case49p 0 3) := .refl
  have hL1 : Reach case49b (exchange case49p 0 3) (exchange (exchange case49p 0 3) 1 2) := hL0.tail ⟨by unfold Valid; decide, 1, 2, 4, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case49b (exchange case49p 1 2) (exchange case49p 1 2) := .refl
  have hR1 : Reach case49b (exchange case49p 1 2) (exchange (exchange case49p 1 2) 0 3) := hR0.tail ⟨by unfold Valid; decide, 0, 3, 4, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case49p 0 3) 1 2) = (exchange (exchange case49p 1 2) 0 3) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case49p 0 3) 1 2),hL1,he ▸ hR1⟩

noncomputable def case50p : Placement 5 := Equiv.ofBijective (![3,0,2,1,4] : Fin 5 → Fin 5) (by decide)
def case50b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case50_strongest : case50b = suffixCap (peakCaps case50p 1 4 3 4) := by
  funext i
  revert i
  decide
theorem case50_join : ∃ z, Reach case50b (exchange case50p 0 1) z ∧ Reach case50b (exchange case50p 2 3) z := by
  have hL0 : Reach case50b (exchange case50p 0 1) (exchange case50p 0 1) := .refl
  have hL1 : Reach case50b (exchange case50p 0 1) (exchange (exchange case50p 0 1) 2 3) := hL0.tail ⟨by unfold Valid; decide, 2, 3, 4, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case50b (exchange case50p 2 3) (exchange case50p 2 3) := .refl
  have hR1 : Reach case50b (exchange case50p 2 3) (exchange (exchange case50p 2 3) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 4, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case50p 0 1) 2 3) = (exchange (exchange case50p 2 3) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case50p 0 1) 2 3),hL1,he ▸ hR1⟩

noncomputable def case51p : Placement 5 := Equiv.ofBijective (![3,1,0,2,4] : Fin 5 → Fin 5) (by decide)
def case51b : Fin 5 → Nat := ![0,0,0,0,1]
theorem case51_strongest : case51b = suffixCap (peakCaps case51p 1 4 2 3) := by
  funext i
  revert i
  decide
theorem case51_join : ∃ z, Reach case51b (exchange case51p 0 1) z ∧ Reach case51b (exchange case51p 1 2) z := by
  have hL0 : Reach case51b (exchange case51p 0 1) (exchange case51p 0 1) := .refl
  have hL1 : Reach case51b (exchange case51p 0 1) (exchange (exchange case51p 0 1) 0 2) := hL0.tail ⟨by unfold Valid; decide, 0, 2, 3, by unfold Legal; decide, rfl⟩
  have hL2 : Reach case51b (exchange case51p 0 1) (exchange (exchange (exchange case51p 0 1) 0 2) 1 2) := hL1.tail ⟨by unfold Valid; decide, 1, 2, 4, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case51b (exchange case51p 1 2) (exchange case51p 1 2) := .refl
  have hR1 : Reach case51b (exchange case51p 1 2) (exchange (exchange case51p 1 2) 0 2) := hR0.tail ⟨by unfold Valid; decide, 0, 2, 4, by unfold Legal; decide, rfl⟩
  have hR2 : Reach case51b (exchange case51p 1 2) (exchange (exchange (exchange case51p 1 2) 0 2) 0 1) := hR1.tail ⟨by unfold Valid; decide, 0, 1, 2, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange (exchange case51p 0 1) 0 2) 1 2) = (exchange (exchange (exchange case51p 1 2) 0 2) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange (exchange case51p 0 1) 0 2) 1 2),hL2,he ▸ hR2⟩

noncomputable def case52p : Placement 5 := Equiv.ofBijective (![3,1,0,2,4] : Fin 5 → Fin 5) (by decide)
def case52b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case52_strongest : case52b = suffixCap (peakCaps case52p 2 4 2 3) := by
  funext i
  revert i
  decide
theorem case52_join : ∃ z, Reach case52b (exchange case52p 0 2) z ∧ Reach case52b (exchange case52p 1 2) z := by
  have hL0 : Reach case52b (exchange case52p 0 2) (exchange case52p 0 2) := .refl
  have hR0 : Reach case52b (exchange case52p 1 2) (exchange case52p 1 2) := .refl
  have hR1 : Reach case52b (exchange case52p 1 2) (exchange (exchange case52p 1 2) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 4, by unfold Legal; decide, rfl⟩
  have hR2 : Reach case52b (exchange case52p 1 2) (exchange (exchange (exchange case52p 1 2) 0 1) 1 2) := hR1.tail ⟨by unfold Valid; decide, 1, 2, 4, by unfold Legal; decide, rfl⟩
  have he : (exchange case52p 0 2) = (exchange (exchange (exchange case52p 1 2) 0 1) 1 2) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange case52p 0 2),hL0,he ▸ hR2⟩

noncomputable def case53p : Placement 5 := Equiv.ofBijective (![3,1,0,2,4] : Fin 5 → Fin 5) (by decide)
def case53b : Fin 5 → Nat := ![0,0,0,0,2]
theorem case53_strongest : case53b = suffixCap (peakCaps case53p 3 4 2 3) := by
  funext i
  revert i
  decide
theorem case53_join : ∃ z, Reach case53b (exchange case53p 0 3) z ∧ Reach case53b (exchange case53p 1 2) z := by
  have hL0 : Reach case53b (exchange case53p 0 3) (exchange case53p 0 3) := .refl
  have hL1 : Reach case53b (exchange case53p 0 3) (exchange (exchange case53p 0 3) 1 2) := hL0.tail ⟨by unfold Valid; decide, 1, 2, 3, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case53b (exchange case53p 1 2) (exchange case53p 1 2) := .refl
  have hR1 : Reach case53b (exchange case53p 1 2) (exchange (exchange case53p 1 2) 0 3) := hR0.tail ⟨by unfold Valid; decide, 0, 3, 4, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case53p 0 3) 1 2) = (exchange (exchange case53p 1 2) 0 3) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case53p 0 3) 1 2),hL1,he ▸ hR1⟩

noncomputable def case54p : Placement 5 := Equiv.ofBijective (![3,1,0,2,4] : Fin 5 → Fin 5) (by decide)
def case54b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case54_strongest : case54b = suffixCap (peakCaps case54p 3 4 2 4) := by
  funext i
  revert i
  decide
theorem case54_join : ∃ z, Reach case54b (exchange case54p 0 3) z ∧ Reach case54b (exchange case54p 1 2) z := by
  have hL0 : Reach case54b (exchange case54p 0 3) (exchange case54p 0 3) := .refl
  have hL1 : Reach case54b (exchange case54p 0 3) (exchange (exchange case54p 0 3) 1 2) := hL0.tail ⟨by unfold Valid; decide, 1, 2, 3, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case54b (exchange case54p 1 2) (exchange case54p 1 2) := .refl
  have hR1 : Reach case54b (exchange case54p 1 2) (exchange (exchange case54p 1 2) 0 3) := hR0.tail ⟨by unfold Valid; decide, 0, 3, 4, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case54p 0 3) 1 2) = (exchange (exchange case54p 1 2) 0 3) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case54p 0 3) 1 2),hL1,he ▸ hR1⟩

noncomputable def case55p : Placement 5 := Equiv.ofBijective (![3,1,0,4,2] : Fin 5 → Fin 5) (by decide)
def case55b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case55_strongest : case55b = suffixCap (peakCaps case55p 1 3 2 4) := by
  funext i
  revert i
  decide
theorem case55_join : ∃ z, Reach case55b (exchange case55p 0 1) z ∧ Reach case55b (exchange case55p 1 2) z := by
  have hL0 : Reach case55b (exchange case55p 0 1) (exchange case55p 0 1) := .refl
  have hL1 : Reach case55b (exchange case55p 0 1) (exchange (exchange case55p 0 1) 0 2) := hL0.tail ⟨by unfold Valid; decide, 0, 2, 3, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case55b (exchange case55p 1 2) (exchange case55p 1 2) := .refl
  have hR1 : Reach case55b (exchange case55p 1 2) (exchange (exchange case55p 1 2) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 3, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case55p 0 1) 0 2) = (exchange (exchange case55p 1 2) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case55p 0 1) 0 2),hL1,he ▸ hR1⟩

noncomputable def case56p : Placement 5 := Equiv.ofBijective (![3,1,0,4,2] : Fin 5 → Fin 5) (by decide)
def case56b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case56_strongest : case56b = suffixCap (peakCaps case56p 2 3 2 4) := by
  funext i
  revert i
  decide
theorem case56_join : ∃ z, Reach case56b (exchange case56p 0 2) z ∧ Reach case56b (exchange case56p 1 2) z := by
  have hL0 : Reach case56b (exchange case56p 0 2) (exchange case56p 0 2) := .refl
  have hR0 : Reach case56b (exchange case56p 1 2) (exchange case56p 1 2) := .refl
  have hR1 : Reach case56b (exchange case56p 1 2) (exchange (exchange case56p 1 2) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 3, by unfold Legal; decide, rfl⟩
  have hR2 : Reach case56b (exchange case56p 1 2) (exchange (exchange (exchange case56p 1 2) 0 1) 1 2) := hR1.tail ⟨by unfold Valid; decide, 1, 2, 3, by unfold Legal; decide, rfl⟩
  have he : (exchange case56p 0 2) = (exchange (exchange (exchange case56p 1 2) 0 1) 1 2) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange case56p 0 2),hL0,he ▸ hR2⟩

noncomputable def case57p : Placement 5 := Equiv.ofBijective (![3,1,2,0,4] : Fin 5 → Fin 5) (by decide)
def case57b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case57_strongest : case57b = suffixCap (peakCaps case57p 1 4 3 4) := by
  funext i
  revert i
  decide
theorem case57_join : ∃ z, Reach case57b (exchange case57p 0 1) z ∧ Reach case57b (exchange case57p 2 3) z := by
  have hL0 : Reach case57b (exchange case57p 0 1) (exchange case57p 0 1) := .refl
  have hL1 : Reach case57b (exchange case57p 0 1) (exchange (exchange case57p 0 1) 2 3) := hL0.tail ⟨by unfold Valid; decide, 2, 3, 4, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case57b (exchange case57p 2 3) (exchange case57p 2 3) := .refl
  have hR1 : Reach case57b (exchange case57p 2 3) (exchange (exchange case57p 2 3) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 4, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case57p 0 1) 2 3) = (exchange (exchange case57p 2 3) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case57p 0 1) 2 3),hL1,he ▸ hR1⟩

noncomputable def case58p : Placement 5 := Equiv.ofBijective (![3,1,2,0,4] : Fin 5 → Fin 5) (by decide)
def case58b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case58_strongest : case58b = suffixCap (peakCaps case58p 2 4 3 4) := by
  funext i
  revert i
  decide
theorem case58_join : ∃ z, Reach case58b (exchange case58p 0 2) z ∧ Reach case58b (exchange case58p 1 3) z := by
  have hL0 : Reach case58b (exchange case58p 0 2) (exchange case58p 0 2) := .refl
  have hL1 : Reach case58b (exchange case58p 0 2) (exchange (exchange case58p 0 2) 1 3) := hL0.tail ⟨by unfold Valid; decide, 1, 3, 4, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case58b (exchange case58p 1 3) (exchange case58p 1 3) := .refl
  have hR1 : Reach case58b (exchange case58p 1 3) (exchange (exchange case58p 1 3) 0 2) := hR0.tail ⟨by unfold Valid; decide, 0, 2, 4, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case58p 0 2) 1 3) = (exchange (exchange case58p 1 3) 0 2) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case58p 0 2) 1 3),hL1,he ▸ hR1⟩

noncomputable def case59p : Placement 5 := Equiv.ofBijective (![3,1,4,0,2] : Fin 5 → Fin 5) (by decide)
def case59b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case59_strongest : case59b = suffixCap (peakCaps case59p 1 2 3 4) := by
  funext i
  revert i
  decide
theorem case59_join : ∃ z, Reach case59b (exchange case59p 0 1) z ∧ Reach case59b (exchange case59p 1 3) z := by
  have hL0 : Reach case59b (exchange case59p 0 1) (exchange case59p 0 1) := .refl
  have hL1 : Reach case59b (exchange case59p 0 1) (exchange (exchange case59p 0 1) 0 3) := hL0.tail ⟨by unfold Valid; decide, 0, 3, 4, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case59b (exchange case59p 1 3) (exchange case59p 1 3) := .refl
  have hR1 : Reach case59b (exchange case59p 1 3) (exchange (exchange case59p 1 3) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 2, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case59p 0 1) 0 3) = (exchange (exchange case59p 1 3) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case59p 0 1) 0 3),hL1,he ▸ hR1⟩

noncomputable def case60p : Placement 5 := Equiv.ofBijective (![3,2,0,1,4] : Fin 5 → Fin 5) (by decide)
def case60b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case60_strongest : case60b = suffixCap (peakCaps case60p 2 4 3 4) := by
  funext i
  revert i
  decide
theorem case60_join : ∃ z, Reach case60b (exchange case60p 0 2) z ∧ Reach case60b (exchange case60p 1 3) z := by
  have hL0 : Reach case60b (exchange case60p 0 2) (exchange case60p 0 2) := .refl
  have hL1 : Reach case60b (exchange case60p 0 2) (exchange (exchange case60p 0 2) 1 3) := hL0.tail ⟨by unfold Valid; decide, 1, 3, 4, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case60b (exchange case60p 1 3) (exchange case60p 1 3) := .refl
  have hR1 : Reach case60b (exchange case60p 1 3) (exchange (exchange case60p 1 3) 0 2) := hR0.tail ⟨by unfold Valid; decide, 0, 2, 4, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case60p 0 2) 1 3) = (exchange (exchange case60p 1 3) 0 2) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case60p 0 2) 1 3),hL1,he ▸ hR1⟩

noncomputable def case61p : Placement 5 := Equiv.ofBijective (![3,2,0,1,4] : Fin 5 → Fin 5) (by decide)
def case61b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case61_strongest : case61b = suffixCap (peakCaps case61p 3 4 2 4) := by
  funext i
  revert i
  decide
theorem case61_join : ∃ z, Reach case61b (exchange case61p 0 3) z ∧ Reach case61b (exchange case61p 1 2) z := by
  have hL0 : Reach case61b (exchange case61p 0 3) (exchange case61p 0 3) := .refl
  have hL1 : Reach case61b (exchange case61p 0 3) (exchange (exchange case61p 0 3) 1 2) := hL0.tail ⟨by unfold Valid; decide, 1, 2, 3, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case61b (exchange case61p 1 2) (exchange case61p 1 2) := .refl
  have hR1 : Reach case61b (exchange case61p 1 2) (exchange (exchange case61p 1 2) 0 3) := hR0.tail ⟨by unfold Valid; decide, 0, 3, 4, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case61p 0 3) 1 2) = (exchange (exchange case61p 1 2) 0 3) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case61p 0 3) 1 2),hL1,he ▸ hR1⟩

noncomputable def case62p : Placement 5 := Equiv.ofBijective (![3,2,1,0,4] : Fin 5 → Fin 5) (by decide)
def case62b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case62_strongest : case62b = suffixCap (peakCaps case62p 1 4 3 4) := by
  funext i
  revert i
  decide
theorem case62_join : ∃ z, Reach case62b (exchange case62p 0 1) z ∧ Reach case62b (exchange case62p 2 3) z := by
  have hL0 : Reach case62b (exchange case62p 0 1) (exchange case62p 0 1) := .refl
  have hL1 : Reach case62b (exchange case62p 0 1) (exchange (exchange case62p 0 1) 2 3) := hL0.tail ⟨by unfold Valid; decide, 2, 3, 4, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case62b (exchange case62p 2 3) (exchange case62p 2 3) := .refl
  have hR1 : Reach case62b (exchange case62p 2 3) (exchange (exchange case62p 2 3) 0 1) := hR0.tail ⟨by unfold Valid; decide, 0, 1, 4, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case62p 0 1) 2 3) = (exchange (exchange case62p 2 3) 0 1) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case62p 0 1) 2 3),hL1,he ▸ hR1⟩

noncomputable def case63p : Placement 5 := Equiv.ofBijective (![3,2,1,0,4] : Fin 5 → Fin 5) (by decide)
def case63b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case63_strongest : case63b = suffixCap (peakCaps case63p 2 4 3 4) := by
  funext i
  revert i
  decide
theorem case63_join : ∃ z, Reach case63b (exchange case63p 0 2) z ∧ Reach case63b (exchange case63p 1 3) z := by
  have hL0 : Reach case63b (exchange case63p 0 2) (exchange case63p 0 2) := .refl
  have hL1 : Reach case63b (exchange case63p 0 2) (exchange (exchange case63p 0 2) 1 3) := hL0.tail ⟨by unfold Valid; decide, 1, 3, 4, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case63b (exchange case63p 1 3) (exchange case63p 1 3) := .refl
  have hR1 : Reach case63b (exchange case63p 1 3) (exchange (exchange case63p 1 3) 0 2) := hR0.tail ⟨by unfold Valid; decide, 0, 2, 4, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case63p 0 2) 1 3) = (exchange (exchange case63p 1 3) 0 2) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case63p 0 2) 1 3),hL1,he ▸ hR1⟩

noncomputable def case64p : Placement 5 := Equiv.ofBijective (![3,2,1,0,4] : Fin 5 → Fin 5) (by decide)
def case64b : Fin 5 → Nat := ![0,0,0,0,0]
theorem case64_strongest : case64b = suffixCap (peakCaps case64p 3 4 2 4) := by
  funext i
  revert i
  decide
theorem case64_join : ∃ z, Reach case64b (exchange case64p 0 3) z ∧ Reach case64b (exchange case64p 1 2) z := by
  have hL0 : Reach case64b (exchange case64p 0 3) (exchange case64p 0 3) := .refl
  have hL1 : Reach case64b (exchange case64p 0 3) (exchange (exchange case64p 0 3) 1 2) := hL0.tail ⟨by unfold Valid; decide, 1, 2, 3, by unfold Legal; decide, rfl⟩
  have hR0 : Reach case64b (exchange case64p 1 2) (exchange case64p 1 2) := .refl
  have hR1 : Reach case64b (exchange case64p 1 2) (exchange (exchange case64p 1 2) 0 3) := hR0.tail ⟨by unfold Valid; decide, 0, 3, 4, by unfold Legal; decide, rfl⟩
  have he : (exchange (exchange case64p 0 3) 1 2) = (exchange (exchange case64p 1 2) 0 3) := by
    apply Equiv.ext
    decide
  exact ⟨(exchange (exchange case64p 0 3) 1 2),hL1,he ▸ hR1⟩
theorem case1_peak : Valid case1b case1p ∧ Legal case1b case1p 0 1 2 ∧ Legal case1b case1p 0 1 3 := by
  unfold Valid Legal
  decide
theorem case2_peak : Valid case2b case2p ∧ Legal case2b case2p 0 1 2 ∧ Legal case2b case2p 0 1 3 := by
  unfold Valid Legal
  decide
theorem case3_peak : Valid case3b case3p ∧ Legal case3b case3p 0 2 3 ∧ Legal case3b case3p 1 2 3 := by
  unfold Valid Legal
  decide
theorem case4_peak : Valid case4b case4p ∧ Legal case4b case4p 0 1 3 ∧ Legal case4b case4p 0 2 3 := by
  unfold Valid Legal
  decide
theorem case5_peak : Valid case5b case5p ∧ Legal case5b case5p 0 1 3 ∧ Legal case5b case5p 0 2 3 := by
  unfold Valid Legal
  decide
theorem case6_peak : Valid case6b case6p ∧ Legal case6b case6p 0 1 3 ∧ Legal case6b case6p 1 2 3 := by
  unfold Valid Legal
  decide
theorem case7_peak : Valid case7b case7p ∧ Legal case7b case7p 0 2 3 ∧ Legal case7b case7p 1 2 3 := by
  unfold Valid Legal
  decide
theorem case8_peak : Valid case8b case8p ∧ Legal case8b case8p 0 1 2 ∧ Legal case8b case8p 2 3 4 := by
  unfold Valid Legal
  decide
theorem case9_peak : Valid case9b case9p ∧ Legal case9b case9p 0 1 3 ∧ Legal case9b case9p 2 3 4 := by
  unfold Valid Legal
  decide
theorem case10_peak : Valid case10b case10p ∧ Legal case10b case10p 0 1 4 ∧ Legal case10b case10p 2 3 4 := by
  unfold Valid Legal
  decide
theorem case11_peak : Valid case11b case11p ∧ Legal case11b case11p 0 2 3 ∧ Legal case11b case11p 1 2 4 := by
  unfold Valid Legal
  decide
theorem case12_peak : Valid case12b case12p ∧ Legal case12b case12p 0 2 4 ∧ Legal case12b case12p 1 2 3 := by
  unfold Valid Legal
  decide
theorem case13_peak : Valid case13b case13p ∧ Legal case13b case13p 0 2 3 ∧ Legal case13b case13p 1 2 4 := by
  unfold Valid Legal
  decide
theorem case14_peak : Valid case14b case14p ∧ Legal case14b case14p 0 2 4 ∧ Legal case14b case14p 1 2 3 := by
  unfold Valid Legal
  decide
theorem case15_peak : Valid case15b case15p ∧ Legal case15b case15p 0 2 3 ∧ Legal case15b case15p 1 2 4 := by
  unfold Valid Legal
  decide
theorem case16_peak : Valid case16b case16p ∧ Legal case16b case16p 0 2 3 ∧ Legal case16b case16p 1 3 4 := by
  unfold Valid Legal
  decide
theorem case17_peak : Valid case17b case17p ∧ Legal case17b case17p 0 2 4 ∧ Legal case17b case17p 1 3 4 := by
  unfold Valid Legal
  decide
theorem case18_peak : Valid case18b case18p ∧ Legal case18b case18p 0 2 4 ∧ Legal case18b case18p 1 2 3 := by
  unfold Valid Legal
  decide
theorem case19_peak : Valid case19b case19p ∧ Legal case19b case19p 0 3 4 ∧ Legal case19b case19p 1 2 4 := by
  unfold Valid Legal
  decide
theorem case20_peak : Valid case20b case20p ∧ Legal case20b case20p 0 1 3 ∧ Legal case20b case20p 0 2 4 := by
  unfold Valid Legal
  decide
theorem case21_peak : Valid case21b case21p ∧ Legal case21b case21p 0 1 4 ∧ Legal case21b case21p 0 2 3 := by
  unfold Valid Legal
  decide
theorem case22_peak : Valid case22b case22p ∧ Legal case22b case22p 0 1 3 ∧ Legal case22b case22p 0 2 4 := by
  unfold Valid Legal
  decide
theorem case23_peak : Valid case23b case23p ∧ Legal case23b case23p 0 1 4 ∧ Legal case23b case23p 0 2 3 := by
  unfold Valid Legal
  decide
theorem case24_peak : Valid case24b case24p ∧ Legal case24b case24p 0 1 2 ∧ Legal case24b case24p 0 3 4 := by
  unfold Valid Legal
  decide
theorem case25_peak : Valid case25b case25p ∧ Legal case25b case25p 0 1 2 ∧ Legal case25b case25p 2 3 4 := by
  unfold Valid Legal
  decide
theorem case26_peak : Valid case26b case26p ∧ Legal case26b case26p 0 1 4 ∧ Legal case26b case26p 2 3 4 := by
  unfold Valid Legal
  decide
theorem case27_peak : Valid case27b case27p ∧ Legal case27b case27p 0 1 2 ∧ Legal case27b case27p 0 3 4 := by
  unfold Valid Legal
  decide
theorem case28_peak : Valid case28b case28p ∧ Legal case28b case28p 0 1 3 ∧ Legal case28b case28p 0 2 4 := by
  unfold Valid Legal
  decide
theorem case29_peak : Valid case29b case29p ∧ Legal case29b case29p 0 1 3 ∧ Legal case29b case29p 1 2 4 := by
  unfold Valid Legal
  decide
theorem case30_peak : Valid case30b case30p ∧ Legal case30b case30p 0 1 4 ∧ Legal case30b case30p 0 2 3 := by
  unfold Valid Legal
  decide
theorem case31_peak : Valid case31b case31p ∧ Legal case31b case31p 0 1 4 ∧ Legal case31b case31p 1 2 3 := by
  unfold Valid Legal
  decide
theorem case32_peak : Valid case32b case32p ∧ Legal case32b case32p 0 2 3 ∧ Legal case32b case32p 1 2 4 := by
  unfold Valid Legal
  decide
theorem case33_peak : Valid case33b case33p ∧ Legal case33b case33p 0 2 4 ∧ Legal case33b case33p 1 2 3 := by
  unfold Valid Legal
  decide
theorem case34_peak : Valid case34b case34p ∧ Legal case34b case34p 0 1 3 ∧ Legal case34b case34p 0 2 4 := by
  unfold Valid Legal
  decide
theorem case35_peak : Valid case35b case35p ∧ Legal case35b case35p 0 1 3 ∧ Legal case35b case35p 1 2 4 := by
  unfold Valid Legal
  decide
theorem case36_peak : Valid case36b case36p ∧ Legal case36b case36p 0 1 4 ∧ Legal case36b case36p 0 2 3 := by
  unfold Valid Legal
  decide
theorem case37_peak : Valid case37b case37p ∧ Legal case37b case37p 0 1 4 ∧ Legal case37b case37p 1 2 3 := by
  unfold Valid Legal
  decide
theorem case38_peak : Valid case38b case38p ∧ Legal case38b case38p 0 2 3 ∧ Legal case38b case38p 1 2 4 := by
  unfold Valid Legal
  decide
theorem case39_peak : Valid case39b case39p ∧ Legal case39b case39p 0 2 4 ∧ Legal case39b case39p 1 2 3 := by
  unfold Valid Legal
  decide
theorem case40_peak : Valid case40b case40p ∧ Legal case40b case40p 0 1 2 ∧ Legal case40b case40p 0 3 4 := by
  unfold Valid Legal
  decide
theorem case41_peak : Valid case41b case41p ∧ Legal case41b case41p 0 1 2 ∧ Legal case41b case41p 1 3 4 := by
  unfold Valid Legal
  decide
theorem case42_peak : Valid case42b case42p ∧ Legal case42b case42p 0 1 2 ∧ Legal case42b case42p 2 3 4 := by
  unfold Valid Legal
  decide
theorem case43_peak : Valid case43b case43p ∧ Legal case43b case43p 0 1 4 ∧ Legal case43b case43p 2 3 4 := by
  unfold Valid Legal
  decide
theorem case44_peak : Valid case44b case44p ∧ Legal case44b case44p 0 1 2 ∧ Legal case44b case44p 0 3 4 := by
  unfold Valid Legal
  decide
theorem case45_peak : Valid case45b case45p ∧ Legal case45b case45p 0 1 2 ∧ Legal case45b case45p 1 3 4 := by
  unfold Valid Legal
  decide
theorem case46_peak : Valid case46b case46p ∧ Legal case46b case46p 0 2 4 ∧ Legal case46b case46p 1 3 4 := by
  unfold Valid Legal
  decide
theorem case47_peak : Valid case47b case47p ∧ Legal case47b case47p 0 3 4 ∧ Legal case47b case47p 1 2 4 := by
  unfold Valid Legal
  decide
theorem case48_peak : Valid case48b case48p ∧ Legal case48b case48p 0 2 4 ∧ Legal case48b case48p 1 3 4 := by
  unfold Valid Legal
  decide
theorem case49_peak : Valid case49b case49p ∧ Legal case49b case49p 0 3 4 ∧ Legal case49b case49p 1 2 4 := by
  unfold Valid Legal
  decide
theorem case50_peak : Valid case50b case50p ∧ Legal case50b case50p 0 1 4 ∧ Legal case50b case50p 2 3 4 := by
  unfold Valid Legal
  decide
theorem case51_peak : Valid case51b case51p ∧ Legal case51b case51p 0 1 4 ∧ Legal case51b case51p 1 2 3 := by
  unfold Valid Legal
  decide
theorem case52_peak : Valid case52b case52p ∧ Legal case52b case52p 0 2 4 ∧ Legal case52b case52p 1 2 3 := by
  unfold Valid Legal
  decide
theorem case53_peak : Valid case53b case53p ∧ Legal case53b case53p 0 3 4 ∧ Legal case53b case53p 1 2 3 := by
  unfold Valid Legal
  decide
theorem case54_peak : Valid case54b case54p ∧ Legal case54b case54p 0 3 4 ∧ Legal case54b case54p 1 2 4 := by
  unfold Valid Legal
  decide
theorem case55_peak : Valid case55b case55p ∧ Legal case55b case55p 0 1 3 ∧ Legal case55b case55p 1 2 4 := by
  unfold Valid Legal
  decide
theorem case56_peak : Valid case56b case56p ∧ Legal case56b case56p 0 2 3 ∧ Legal case56b case56p 1 2 4 := by
  unfold Valid Legal
  decide
theorem case57_peak : Valid case57b case57p ∧ Legal case57b case57p 0 1 4 ∧ Legal case57b case57p 2 3 4 := by
  unfold Valid Legal
  decide
theorem case58_peak : Valid case58b case58p ∧ Legal case58b case58p 0 2 4 ∧ Legal case58b case58p 1 3 4 := by
  unfold Valid Legal
  decide
theorem case59_peak : Valid case59b case59p ∧ Legal case59b case59p 0 1 2 ∧ Legal case59b case59p 1 3 4 := by
  unfold Valid Legal
  decide
theorem case60_peak : Valid case60b case60p ∧ Legal case60b case60p 0 2 4 ∧ Legal case60b case60p 1 3 4 := by
  unfold Valid Legal
  decide
theorem case61_peak : Valid case61b case61p ∧ Legal case61b case61p 0 3 4 ∧ Legal case61b case61p 1 2 4 := by
  unfold Valid Legal
  decide
theorem case62_peak : Valid case62b case62p ∧ Legal case62b case62p 0 1 4 ∧ Legal case62b case62p 2 3 4 := by
  unfold Valid Legal
  decide
theorem case63_peak : Valid case63b case63p ∧ Legal case63b case63p 0 2 4 ∧ Legal case63b case63p 1 3 4 := by
  unfold Valid Legal
  decide
theorem case64_peak : Valid case64b case64p ∧ Legal case64b case64p 0 3 4 ∧ Legal case64b case64p 1 2 4 := by
  unfold Valid Legal
  decide
end Young213
```

```lean module=YoungAudit.lean
import YoungSource
#print Young213.partial_endpoint
#print axioms Young213.exchange_apply
#print axioms Young213.occurrence_iff
#print axioms Young213.valid_exchange
#print axioms Young213.step_valid
#print axioms Young213.terminal_iff_avoid
#print axioms Young213.monotone_below_caps_iff
#print axioms Young213.swap_embed
#print axioms Young213.exchange_agrees
#print axioms Young213.exchange_outside
#print axioms Young213.legal_compression
#print axioms Young213.lift_step
#print axioms Young213.lift_path
#print axioms Young213.fitting_nonempty
#print axioms Young213.threshold_spec
#print axioms Young213.threshold_monotone
#print axioms Young213.split_sum
#print axioms Young213.weight_decreases
#print axioms Young213.step_weight
#print axioms Young213.terminating
#print axioms Young213.terminal_exists
#print axioms Young213.suffixCap_le
#print axioms Young213.le_suffixCap
#print axioms Young213.suffixCap_monotone
#print axioms Young213.suffixCap_greatest
#print axioms Young213.peakCaps_iff
#print axioms Young213.strongest_boundary
#print axioms Young213.step_boundary_mono
#print axioms Young213.reach_boundary_mono
#print axioms Young213.exchange_commute
#print axioms Young213.strongest_admissible
#print axioms Young213.disjoint_legal
#print axioms Young213.disjoint_join
#print axioms Young213.graph_transversal
#print axioms Young213.transversal_encoding
#print axioms Young213.graph_occurrence
#print axioms Young213.source_step_iff
#print axioms Young213.source_step_extract
#print axioms Young213.source_path_extract
#print axioms Young213.source_path_iff
#print axioms Young213.partial_endpoint
```

```lean module=YoungCompleteAudit.lean
import YoungSequences
#print Young213.source_shape_complete
#print axioms Young213.source_shape_complete
#print axioms Young213.path_sequence
#print axioms Young213.peakCaps_symm
#print axioms Young213.strongest_symm
```

```lean module=YoungContinuationAudit.lean
import YoungTableJoins
import YoungAudit
-- Partial continuation only: no complete endpoint exists in these modules.
#print Young213.compress_peak
#print Young213.tripleSupport_cases
#print Young213.rank_coverage4
#print Young213.rank_coverage5
#print Young213.table_join4
#print Young213.table_join5
#print Young213.partial_endpoint
#print axioms Young213.ordered_support
#print axioms Young213.compressed_support
#print axioms Young213.agrees_ext
#print axioms Young213.lift_join
#print axioms Young213.tripleSupport_card
#print axioms Young213.tripleSupport_eq
#print axioms Young213.tripleSupport_cases
#print axioms Young213.compress_peak
#print axioms Young213.case1_strongest
#print axioms Young213.case1_join
#print axioms Young213.case2_strongest
#print axioms Young213.case2_join
#print axioms Young213.case3_strongest
#print axioms Young213.case3_join
#print axioms Young213.case4_strongest
#print axioms Young213.case4_join
#print axioms Young213.case5_strongest
#print axioms Young213.case5_join
#print axioms Young213.case6_strongest
#print axioms Young213.case6_join
#print axioms Young213.case7_strongest
#print axioms Young213.case7_join
#print axioms Young213.case8_strongest
#print axioms Young213.case8_join
#print axioms Young213.case9_strongest
#print axioms Young213.case9_join
#print axioms Young213.case10_strongest
#print axioms Young213.case10_join
#print axioms Young213.case11_strongest
#print axioms Young213.case11_join
#print axioms Young213.case12_strongest
#print axioms Young213.case12_join
#print axioms Young213.case13_strongest
#print axioms Young213.case13_join
#print axioms Young213.case14_strongest
#print axioms Young213.case14_join
#print axioms Young213.case15_strongest
#print axioms Young213.case15_join
#print axioms Young213.case16_strongest
#print axioms Young213.case16_join
#print axioms Young213.case17_strongest
#print axioms Young213.case17_join
#print axioms Young213.case18_strongest
#print axioms Young213.case18_join
#print axioms Young213.case19_strongest
#print axioms Young213.case19_join
#print axioms Young213.case20_strongest
#print axioms Young213.case20_join
#print axioms Young213.case21_strongest
#print axioms Young213.case21_join
#print axioms Young213.case22_strongest
#print axioms Young213.case22_join
#print axioms Young213.case23_strongest
#print axioms Young213.case23_join
#print axioms Young213.case24_strongest
#print axioms Young213.case24_join
#print axioms Young213.case25_strongest
#print axioms Young213.case25_join
#print axioms Young213.case26_strongest
#print axioms Young213.case26_join
#print axioms Young213.case27_strongest
#print axioms Young213.case27_join
#print axioms Young213.case28_strongest
#print axioms Young213.case28_join
#print axioms Young213.case29_strongest
#print axioms Young213.case29_join
#print axioms Young213.case30_strongest
#print axioms Young213.case30_join
#print axioms Young213.case31_strongest
#print axioms Young213.case31_join
#print axioms Young213.case32_strongest
#print axioms Young213.case32_join
#print axioms Young213.case33_strongest
#print axioms Young213.case33_join
#print axioms Young213.case34_strongest
#print axioms Young213.case34_join
#print axioms Young213.case35_strongest
#print axioms Young213.case35_join
#print axioms Young213.case36_strongest
#print axioms Young213.case36_join
#print axioms Young213.case37_strongest
#print axioms Young213.case37_join
#print axioms Young213.case38_strongest
#print axioms Young213.case38_join
#print axioms Young213.case39_strongest
#print axioms Young213.case39_join
#print axioms Young213.case40_strongest
#print axioms Young213.case40_join
#print axioms Young213.case41_strongest
#print axioms Young213.case41_join
#print axioms Young213.case42_strongest
#print axioms Young213.case42_join
#print axioms Young213.case43_strongest
#print axioms Young213.case43_join
#print axioms Young213.case44_strongest
#print axioms Young213.case44_join
#print axioms Young213.case45_strongest
#print axioms Young213.case45_join
#print axioms Young213.case46_strongest
#print axioms Young213.case46_join
#print axioms Young213.case47_strongest
#print axioms Young213.case47_join
#print axioms Young213.case48_strongest
#print axioms Young213.case48_join
#print axioms Young213.case49_strongest
#print axioms Young213.case49_join
#print axioms Young213.case50_strongest
#print axioms Young213.case50_join
#print axioms Young213.case51_strongest
#print axioms Young213.case51_join
#print axioms Young213.case52_strongest
#print axioms Young213.case52_join
#print axioms Young213.case53_strongest
#print axioms Young213.case53_join
#print axioms Young213.case54_strongest
#print axioms Young213.case54_join
#print axioms Young213.case55_strongest
#print axioms Young213.case55_join
#print axioms Young213.case56_strongest
#print axioms Young213.case56_join
#print axioms Young213.case57_strongest
#print axioms Young213.case57_join
#print axioms Young213.case58_strongest
#print axioms Young213.case58_join
#print axioms Young213.case59_strongest
#print axioms Young213.case59_join
#print axioms Young213.case60_strongest
#print axioms Young213.case60_join
#print axioms Young213.case61_strongest
#print axioms Young213.case61_join
#print axioms Young213.case62_strongest
#print axioms Young213.case62_join
#print axioms Young213.case63_strongest
#print axioms Young213.case63_join
#print axioms Young213.case64_strongest
#print axioms Young213.case64_join
#print axioms Young213.case1_peak
#print axioms Young213.case2_peak
#print axioms Young213.case3_peak
#print axioms Young213.case4_peak
#print axioms Young213.case5_peak
#print axioms Young213.case6_peak
#print axioms Young213.case7_peak
#print axioms Young213.case8_peak
#print axioms Young213.case9_peak
#print axioms Young213.case10_peak
#print axioms Young213.case11_peak
#print axioms Young213.case12_peak
#print axioms Young213.case13_peak
#print axioms Young213.case14_peak
#print axioms Young213.case15_peak
#print axioms Young213.case16_peak
#print axioms Young213.case17_peak
#print axioms Young213.case18_peak
#print axioms Young213.case19_peak
#print axioms Young213.case20_peak
#print axioms Young213.case21_peak
#print axioms Young213.case22_peak
#print axioms Young213.case23_peak
#print axioms Young213.case24_peak
#print axioms Young213.case25_peak
#print axioms Young213.case26_peak
#print axioms Young213.case27_peak
#print axioms Young213.case28_peak
#print axioms Young213.case29_peak
#print axioms Young213.case30_peak
#print axioms Young213.case31_peak
#print axioms Young213.case32_peak
#print axioms Young213.case33_peak
#print axioms Young213.case34_peak
#print axioms Young213.case35_peak
#print axioms Young213.case36_peak
#print axioms Young213.case37_peak
#print axioms Young213.case38_peak
#print axioms Young213.case39_peak
#print axioms Young213.case40_peak
#print axioms Young213.case41_peak
#print axioms Young213.case42_peak
#print axioms Young213.case43_peak
#print axioms Young213.case44_peak
#print axioms Young213.case45_peak
#print axioms Young213.case46_peak
#print axioms Young213.case47_peak
#print axioms Young213.case48_peak
#print axioms Young213.case49_peak
#print axioms Young213.case50_peak
#print axioms Young213.case51_peak
#print axioms Young213.case52_peak
#print axioms Young213.case53_peak
#print axioms Young213.case54_peak
#print axioms Young213.case55_peak
#print axioms Young213.case56_peak
#print axioms Young213.case57_peak
#print axioms Young213.case58_peak
#print axioms Young213.case59_peak
#print axioms Young213.case60_peak
#print axioms Young213.case61_peak
#print axioms Young213.case62_peak
#print axioms Young213.case63_peak
#print axioms Young213.case64_peak
#print axioms Young213.rank_coverage4
#print axioms Young213.rank_coverage5
#print axioms Young213.table_join4
#print axioms Young213.table_join5
#print axioms Young213.partial_endpoint
```

```lean module=YoungCoverage.lean
import Young64
import Mathlib.Data.Fintype.Pi
set_option synthInstance.maxSize 100000
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Young213
def triples4 : Fin 4 → (Fin 4 × Fin 4 × Fin 4) := ![(0,1,2),(0,1,3),(0,2,3),(1,2,3)]
noncomputable def rankCases4 : List ((Fin 4 → Fin 4) × (Fin 4 × Fin 4 × Fin 4) × (Fin 4 × Fin 4 × Fin 4)) := [((case1p : Fin 4 → Fin 4), (0,1,2), (0,1,3)),((case2p : Fin 4 → Fin 4), (0,1,2), (0,1,3)),((case3p : Fin 4 → Fin 4), (0,2,3), (1,2,3)),((case4p : Fin 4 → Fin 4), (0,1,3), (0,2,3)),((case5p : Fin 4 → Fin 4), (0,1,3), (0,2,3)),((case6p : Fin 4 → Fin 4), (0,1,3), (1,2,3)),((case7p : Fin 4 → Fin 4), (0,2,3), (1,2,3))]
theorem rank_coverage4 : ∀ (f : Fin 4 → Fin 4), Function.Bijective f →
    ∀ a b : Fin 4,
    let t := triples4 a
    let u := triples4 b
    f t.2.1 < f t.1 → f t.1 < f t.2.2 →
    f u.2.1 < f u.1 → f u.1 < f u.2.2 →
    (∀ x : Fin 4, x = t.1 ∨ x = t.2.1 ∨ x = t.2.2 ∨
      x = u.1 ∨ x = u.2.1 ∨ x = u.2.2) →
    (f,t,u) ∈ rankCases4 ∨ (f,u,t) ∈ rankCases4 := by
  unfold Function.Bijective Function.Injective Function.Surjective
  dsimp only
  decide
def triples5 : Fin 10 → (Fin 5 × Fin 5 × Fin 5) := ![(0,1,2),(0,1,3),(0,1,4),(0,2,3),(0,2,4),(0,3,4),(1,2,3),(1,2,4),(1,3,4),(2,3,4)]
noncomputable def rankCases5 : List ((Fin 5 → Fin 5) × (Fin 5 × Fin 5 × Fin 5) × (Fin 5 × Fin 5 × Fin 5)) := [((case8p : Fin 5 → Fin 5), (0,1,2), (2,3,4)),((case9p : Fin 5 → Fin 5), (0,1,3), (2,3,4)),((case10p : Fin 5 → Fin 5), (0,1,4), (2,3,4)),((case11p : Fin 5 → Fin 5), (0,2,3), (1,2,4)),((case12p : Fin 5 → Fin 5), (0,2,4), (1,2,3)),((case13p : Fin 5 → Fin 5), (0,2,3), (1,2,4)),((case14p : Fin 5 → Fin 5), (0,2,4), (1,2,3)),((case15p : Fin 5 → Fin 5), (0,2,3), (1,2,4)),((case16p : Fin 5 → Fin 5), (0,2,3), (1,3,4)),((case17p : Fin 5 → Fin 5), (0,2,4), (1,3,4)),((case18p : Fin 5 → Fin 5), (0,2,4), (1,2,3)),((case19p : Fin 5 → Fin 5), (0,3,4), (1,2,4)),((case20p : Fin 5 → Fin 5), (0,1,3), (0,2,4)),((case21p : Fin 5 → Fin 5), (0,1,4), (0,2,3)),((case22p : Fin 5 → Fin 5), (0,1,3), (0,2,4)),((case23p : Fin 5 → Fin 5), (0,1,4), (0,2,3)),((case24p : Fin 5 → Fin 5), (0,1,2), (0,3,4)),((case25p : Fin 5 → Fin 5), (0,1,2), (2,3,4)),((case26p : Fin 5 → Fin 5), (0,1,4), (2,3,4)),((case27p : Fin 5 → Fin 5), (0,1,2), (0,3,4)),((case28p : Fin 5 → Fin 5), (0,1,3), (0,2,4)),((case29p : Fin 5 → Fin 5), (0,1,3), (1,2,4)),((case30p : Fin 5 → Fin 5), (0,1,4), (0,2,3)),((case31p : Fin 5 → Fin 5), (0,1,4), (1,2,3)),((case32p : Fin 5 → Fin 5), (0,2,3), (1,2,4)),((case33p : Fin 5 → Fin 5), (0,2,4), (1,2,3)),((case34p : Fin 5 → Fin 5), (0,1,3), (0,2,4)),((case35p : Fin 5 → Fin 5), (0,1,3), (1,2,4)),((case36p : Fin 5 → Fin 5), (0,1,4), (0,2,3)),((case37p : Fin 5 → Fin 5), (0,1,4), (1,2,3)),((case38p : Fin 5 → Fin 5), (0,2,3), (1,2,4)),((case39p : Fin 5 → Fin 5), (0,2,4), (1,2,3)),((case40p : Fin 5 → Fin 5), (0,1,2), (0,3,4)),((case41p : Fin 5 → Fin 5), (0,1,2), (1,3,4)),((case42p : Fin 5 → Fin 5), (0,1,2), (2,3,4)),((case43p : Fin 5 → Fin 5), (0,1,4), (2,3,4)),((case44p : Fin 5 → Fin 5), (0,1,2), (0,3,4)),((case45p : Fin 5 → Fin 5), (0,1,2), (1,3,4)),((case46p : Fin 5 → Fin 5), (0,2,4), (1,3,4)),((case47p : Fin 5 → Fin 5), (0,3,4), (1,2,4)),((case48p : Fin 5 → Fin 5), (0,2,4), (1,3,4)),((case49p : Fin 5 → Fin 5), (0,3,4), (1,2,4)),((case50p : Fin 5 → Fin 5), (0,1,4), (2,3,4)),((case51p : Fin 5 → Fin 5), (0,1,4), (1,2,3)),((case52p : Fin 5 → Fin 5), (0,2,4), (1,2,3)),((case53p : Fin 5 → Fin 5), (0,3,4), (1,2,3)),((case54p : Fin 5 → Fin 5), (0,3,4), (1,2,4)),((case55p : Fin 5 → Fin 5), (0,1,3), (1,2,4)),((case56p : Fin 5 → Fin 5), (0,2,3), (1,2,4)),((case57p : Fin 5 → Fin 5), (0,1,4), (2,3,4)),((case58p : Fin 5 → Fin 5), (0,2,4), (1,3,4)),((case59p : Fin 5 → Fin 5), (0,1,2), (1,3,4)),((case60p : Fin 5 → Fin 5), (0,2,4), (1,3,4)),((case61p : Fin 5 → Fin 5), (0,3,4), (1,2,4)),((case62p : Fin 5 → Fin 5), (0,1,4), (2,3,4)),((case63p : Fin 5 → Fin 5), (0,2,4), (1,3,4)),((case64p : Fin 5 → Fin 5), (0,3,4), (1,2,4))]
theorem rank_coverage5 : ∀ (f : Fin 5 → Fin 5), Function.Bijective f →
    ∀ a b : Fin 10,
    let t := triples5 a
    let u := triples5 b
    f t.2.1 < f t.1 → f t.1 < f t.2.2 →
    f u.2.1 < f u.1 → f u.1 < f u.2.2 →
    (∀ x : Fin 5, x = t.1 ∨ x = t.2.1 ∨ x = t.2.2 ∨
      x = u.1 ∨ x = u.2.1 ∨ x = u.2.2) →
    (f,t,u) ∈ rankCases5 ∨ (f,u,t) ∈ rankCases5 := by
  unfold Function.Bijective Function.Injective Function.Surjective
  dsimp only
  decide
end Young213
```

```lean module=YoungEndpoint.lean
import YoungPartition
namespace Young213

noncomputable def RowShape.encode {n} (Y : RowShape n) (D : Dots n) : Placement n := by
  classical
  exact if h : Y.Transversal D then
    Classical.choose (ExistsUnique.exists (transversal_encoding ((Y.transversal_iff D).mp h)))
  else Equiv.refl _

theorem RowShape.encode_spec {n} (Y : RowShape n) (D : Dots n) (h : Y.Transversal D) :
    Valid Y.boundary (Y.encode D) ∧ graph (Y.encode D) = D := by
  classical
  simpa only [RowShape.encode,dite_eq_left h] using
    Classical.choose_spec (ExistsUnique.exists (transversal_encoding ((Y.transversal_iff D).mp h)))

theorem RowShape.move_valid {n} (Y : RowShape n) {D E : Dots n} (h : Y.Move D E) :
    Y.Transversal E := by
  obtain ⟨p,⟨hp,hg⟩,_⟩ := transversal_encoding ((Y.transversal_iff D).mp h.1)
  rw [← hg] at h
  obtain ⟨q,hq,rfl⟩ := source_step_extract Y.boundary_monotone p ((Y.move_iff _ _).mp h)
  exact (Y.transversal_iff _).mpr ((graph_transversal q).mpr (step_valid Y.boundary_monotone hq))

theorem RowShape.move_encode {n} (Y : RowShape n) {D E : Dots n} (h : Y.Move D E) :
    Step Y.boundary (Y.encode D) (Y.encode E) := by
  apply (source_step_iff Y.boundary_monotone _ _).mp
  rw [(Y.encode_spec D h.1).2,(Y.encode_spec E (Y.move_valid h)).2]
  exact (Y.move_iff D E).mp h

theorem RowShape.no_infinite_moves {n} (Y : RowShape n) (f : Nat → Dots n)
    (hf : ∀ t, Y.Move (f t) (f (t+1))) : False :=
  Young213.no_infinite_moves (fun t => Y.encode (f t)) (fun t => Y.move_encode (hf t))

def RowShape.Maximal {n} (Y : RowShape n) (D : Dots n)
    (length : Nat) (f : Nat → Dots n) : Prop :=
  f 0 = D ∧ (∀ t, t < length → Y.Move (f t) (f (t+1))) ∧
    ¬ ∃ E, Y.Move (f length) E

theorem RowShape.maximal_paths {n} (Y : RowShape n) {D : Dots n}
    {length : Nat} {f : Nat → Dots n} (hf : Y.Maximal D length f) :
    Y.Paths D (f length) := by
  have h : ∀ t, t ≤ length → Y.Paths D (f t) := by
    intro t
    induction t with
    | zero => intro _; rw [hf.1]
    | succ t ih => intro ht; exact (ih (by omega)).tail (hf.2.1 t (by omega))
  exact h length le_rfl

theorem RowShape.terminal_iff_avoids {n} (Y : RowShape n) {D : Dots n}
    (hD : Y.Transversal D) : (¬ ∃ E, Y.Move D E) ↔ Y.Avoids D := by
  obtain ⟨p,⟨hp,hg⟩,_⟩ := transversal_encoding ((Y.transversal_iff D).mp hD)
  subst D
  rw [Y.graph_avoids,← terminal_iff_avoid hp]
  constructor
  · intro ht ⟨q,hq⟩
    exact ht ⟨graph q,(Y.move_iff _ _).mpr ((source_step_iff Y.boundary_monotone _ _).mpr hq)⟩
  · intro ht ⟨E,hE⟩
    obtain ⟨q,hq,_⟩ := source_step_extract Y.boundary_monotone p ((Y.move_iff _ _).mp hE)
    exact ht ⟨q,hq⟩

theorem RowShape.paths_valid {n} (Y : RowShape n) {D E : Dots n}
    (hD : Y.Transversal D) (h : Y.Paths D E) : Y.Transversal E := by
  induction h with
  | refl => exact hD
  | tail _ hs _ => exact Y.move_valid hs

theorem RowShape.confluence {n} (Y : RowShape n) {D E F : Dots n}
    (hD : Y.Transversal D) (hE : Y.Paths D E) (hF : Y.Paths D F) :
    ∃ G, Y.Paths E G ∧ Y.Paths F G := by
  obtain ⟨p,⟨hp,hg⟩,_⟩ := transversal_encoding ((Y.transversal_iff D).mp hD)
  subst D
  obtain ⟨q,hq,rfl⟩ := source_path_extract Y.boundary_monotone ((Y.paths_iff _ _).mp hE)
  obtain ⟨r,hr,rfl⟩ := source_path_extract Y.boundary_monotone ((Y.paths_iff _ _).mp hF)
  obtain ⟨z,hz1,hz2⟩ := Young213.confluence Y.boundary_monotone hp hq hr
  exact ⟨graph z,(Y.paths_iff _ _).mpr ((source_path_iff Y.boundary_monotone _ _).mpr hz1),
    (Y.paths_iff _ _).mpr ((source_path_iff Y.boundary_monotone _ _).mpr hz2)⟩

/-- Source-shaped all-n endpoint, with no local-confluence or certificate premise. -/
theorem source_shape_endpoint {n} (Y : RowShape n) (D : Dots n) (hD : Y.Transversal D) :
    (∃! E, Y.Paths D E ∧ Y.Transversal E ∧ Y.Avoids E) ∧
    (∀ f : Nat → Dots n, (∀ t, Y.Move (f t) (f (t+1))) → False) ∧
    (∃ E, Y.Paths D E ∧ Y.Transversal E ∧ Y.Avoids E ∧
      ∀ length f, Y.Maximal D length f → f length = E) := by
  refine ⟨Y.unique_endpoint D hD,Y.no_infinite_moves,?_⟩
  obtain ⟨E,hE,hu⟩ := Y.unique_endpoint D hD
  refine ⟨E,hE.1,hE.2.1,hE.2.2,?_⟩
  intro length f hf
  have hr := Y.maximal_paths hf
  have hv := Y.paths_valid hD hr
  exact hu (f length) ⟨hr,hv,(Y.terminal_iff_avoids hv).mp hf.2.2⟩
end Young213
```

```lean module=YoungEndpointAudit.lean
import YoungEndpoint
#print Young213.source_shape_endpoint
#print Young213.RowShape
#print Young213.RowShape.Cell
#print Young213.RowShape.Move
#print Young213.RowShape.Maximal
#print axioms Young213.triples4_complete
#print axioms Young213.triples5_complete
#print axioms Young213.full_join4
#print axioms Young213.full_join5
#print axioms Young213.preimages_cover
#print axioms Young213.overlap_join
#print axioms Young213.legal_join
#print axioms Young213.local_confluence
#print axioms Young213.reach_valid
#print axioms Young213.terminal_reach_eq
#print axioms Young213.avoiding_unique
#print axioms Young213.confluence
#print axioms Young213.unique_normal_form
#print axioms Young213.no_infinite_moves
#print axioms Young213.maximal_reaches
#print axioms Young213.all_maximal_endpoint
#print axioms Young213.RowShape.boundary_cell
#print axioms Young213.RowShape.boundary_monotone
#print axioms Young213.RowShape.proper_iff
#print axioms Young213.RowShape.coordinates
#print axioms Young213.RowShape.transversal_iff
#print axioms Young213.RowShape.occurrence_iff
#print axioms Young213.RowShape.move_iff
#print axioms Young213.RowShape.paths_iff
#print axioms Young213.RowShape.graph_avoids
#print axioms Young213.RowShape.unique_endpoint
#print axioms Young213.RowShape.encode_spec
#print axioms Young213.RowShape.move_valid
#print axioms Young213.RowShape.move_encode
#print axioms Young213.RowShape.no_infinite_moves
#print axioms Young213.RowShape.maximal_paths
#print axioms Young213.RowShape.terminal_iff_avoids
#print axioms Young213.RowShape.paths_valid
#print axioms Young213.RowShape.confluence
#print axioms Young213.source_shape_endpoint
```

```lean module=YoungGlobal.lean
import YoungIntegration
namespace Young213

theorem reach_valid {n} {b : Fin n → Nat} (hb : Monotone b)
    {p q : Placement n} (hp : Valid b p) (h : Reach b p q) : Valid b q := by
  induction h with
  | refl => exact hp
  | tail _ hs _ => exact step_valid hb hs

theorem terminal_reach_eq {n} {b : Fin n → Nat} {p q : Placement n}
    (ht : Terminal b p) (h : Reach b p q) : q = p := by
  rcases h.cases_head with he | ⟨r,hs,_⟩
  · exact he.symm
  · exact (ht ⟨r,hs⟩).elim

theorem avoiding_unique {n} {b : Fin n → Nat} (hb : Monotone b) :
    ∀ p : Placement n, Valid b p → ∀ q r,
    Reach b p q → Reach b p r → Avoid213 b q → Avoid213 b r → q = r := by
  intro p
  induction p using (terminating b).induction with
  | h p ih =>
    intro hp q r hq hr aq ar
    rcases hq.cases_head with he | ⟨x,hx,hxq⟩
    · subst q
      exact (terminal_reach_eq ((terminal_iff_avoid hp).mpr aq) hr).symm
    rcases hr.cases_head with he | ⟨y,hy,hyr⟩
    · subst r
      exact terminal_reach_eq ((terminal_iff_avoid hp).mpr ar) hq
    obtain ⟨z,hxz,hyz⟩ := local_confluence hb hx hy
    obtain ⟨t,hzt,_,hat⟩ := terminal_exists hb z (reach_valid hb (step_valid hb hx) hxz)
    exact (ih x hx (step_valid hb hx) q t hxq (hxz.trans hzt) aq hat).trans
      (ih y hy (step_valid hb hy) r t hyr (hyz.trans hzt) ar hat).symm

theorem confluence {n} {b : Fin n → Nat} (hb : Monotone b)
    {p q r : Placement n} (hp : Valid b p) (hq : Reach b p q) (hr : Reach b p r) :
    ∃ z, Reach b q z ∧ Reach b r z := by
  obtain ⟨u,hqu,_,au⟩ := terminal_exists hb q (reach_valid hb hp hq)
  obtain ⟨v,hrv,_,av⟩ := terminal_exists hb r (reach_valid hb hp hr)
  have he := avoiding_unique hb p hp u v (hq.trans hqu) (hr.trans hrv) au av
  exact ⟨u,hqu,he ▸ hrv⟩

theorem unique_normal_form {n} {b : Fin n → Nat} (hb : Monotone b)
    (p : Placement n) (hp : Valid b p) :
    ∃! t, Reach b p t ∧ Valid b t ∧ Avoid213 b t := by
  obtain ⟨t,ht,hv,ha⟩ := terminal_exists hb p hp
  exact ⟨t,⟨ht,hv,ha⟩,fun q hq => avoiding_unique hb p hp q t hq.1 ht hq.2.2 ha⟩

theorem no_infinite_moves {n} {b : Fin n → Nat} (f : Nat → Placement n)
    (hf : ∀ t, Step b (f t) (f (t+1))) : False := by
  have hbound : ∀ t, weight (f t) + t ≤ weight (f 0) := by
    intro t
    induction t with
    | zero => omega
    | succ t ih => have h := step_weight (hf t); omega
  have h := hbound (weight (f 0)+1)
  omega

def MaximalFinite {n} (b : Fin n → Nat) (p : Placement n)
    (length : Nat) (f : Nat → Placement n) : Prop :=
  f 0 = p ∧ (∀ t, t < length → Step b (f t) (f (t+1))) ∧ Terminal b (f length)

theorem maximal_reaches {n} {b : Fin n → Nat} {p : Placement n}
    {length : Nat} {f : Nat → Placement n} (hf : MaximalFinite b p length f) :
    Reach b p (f length) := by
  have h : ∀ t, t ≤ length → Reach b p (f t) := by
    intro t
    induction t with
    | zero => intro _; rw [hf.1]; exact .refl
    | succ t ih => intro ht; exact (ih (by omega)).tail (hf.2.1 t (by omega))
  exact h length le_rfl

theorem all_maximal_endpoint {n} {b : Fin n → Nat} (hb : Monotone b)
    (p : Placement n) (hp : Valid b p) :
    ∃ t, Reach b p t ∧ Valid b t ∧ Avoid213 b t ∧
    ∀ length f, MaximalFinite b p length f → f length = t := by
  obtain ⟨t,ht,hv,ha⟩ := terminal_exists hb p hp
  refine ⟨t,ht,hv,ha,?_⟩
  intro length f hf
  have hr := maximal_reaches hf
  exact avoiding_unique hb p hp (f length) t hr ht
    ((terminal_iff_avoid (reach_valid hb hp hr)).mp hf.2.2) ha
end Young213
```

```lean module=YoungIntegration.lean
import YoungTableJoins
namespace Young213

theorem triples4_complete : ∀ i j k : Fin 4, i < j → j < k →
    ∃ a, triples4 a = (i,j,k) := by decide

theorem triples5_complete : ∀ i j k : Fin 5, i < j → j < k →
    ∃ a, triples5 a = (i,j,k) := by decide

def FullJoin (m : Nat) : Prop :=
  ∀ (d : Fin m → Nat), Monotone d → ∀ (p : Placement m), Valid d p →
  ∀ i j k I J K, Legal d p i j k → Legal d p I J K →
  (∀ x, x = i ∨ x = j ∨ x = k ∨ x = I ∨ x = J ∨ x = K) →
  ∃ z, Reach d (exchange p i j) z ∧ Reach d (exchange p I J) z

theorem full_join4 : FullJoin 4 := by
  intro d hd p hp i j k I J K h1 h2 hc
  obtain ⟨a,ha⟩ := triples4_complete i j k h1.1 h1.2.1
  obtain ⟨b,hb⟩ := triples4_complete I J K h2.1 h2.2.1
  have hcov := rank_coverage4 p p.bijective a b
  simp only [ha,hb] at hcov
  rcases hcov h1.2.2.2.1 h1.2.2.2.2 h2.2.2.2.1 h2.2.2.2.2 hc with ht | ht
  · obtain ⟨z,hz1,hz2⟩ := table_join4 p (i,j,k) (I,J,K) ht
    have hle := (strongest_boundary p d hd j k J K).mp ⟨hp,h1.2.2.1,h2.2.2.1⟩
    exact ⟨z,reach_boundary_mono hle hz1,reach_boundary_mono hle hz2⟩
  · obtain ⟨z,hz2,hz1⟩ := table_join4 p (I,J,K) (i,j,k) ht
    have hle := (strongest_boundary p d hd J K j k).mp ⟨hp,h2.2.2.1,h1.2.2.1⟩
    exact ⟨z,reach_boundary_mono hle hz1,reach_boundary_mono hle hz2⟩

theorem full_join5 : FullJoin 5 := by
  intro d hd p hp i j k I J K h1 h2 hc
  obtain ⟨a,ha⟩ := triples5_complete i j k h1.1 h1.2.1
  obtain ⟨b,hb⟩ := triples5_complete I J K h2.1 h2.2.1
  have hcov := rank_coverage5 p p.bijective a b
  simp only [ha,hb] at hcov
  rcases hcov h1.2.2.2.1 h1.2.2.2.2 h2.2.2.2.1 h2.2.2.2.2 hc with ht | ht
  · obtain ⟨z,hz1,hz2⟩ := table_join5 p (i,j,k) (I,J,K) ht
    have hle := (strongest_boundary p d hd j k J K).mp ⟨hp,h1.2.2.1,h2.2.2.1⟩
    exact ⟨z,reach_boundary_mono hle hz1,reach_boundary_mono hle hz2⟩
  · obtain ⟨z,hz2,hz1⟩ := table_join5 p (I,J,K) (i,j,k) ht
    have hle := (strongest_boundary p d hd J K j k).mp ⟨hp,h2.2.2.1,h1.2.2.1⟩
    exact ⟨z,reach_boundary_mono hle hz1,reach_boundary_mono hle hz2⟩

theorem preimages_cover {m n} (e : Fin m ↪o Fin n)
    (i j k I J K : Fin n) (a c w A C W : Fin m)
    (he : Set.range e = (↑(tripleSupport i j k ∪ tripleSupport I J K) : Set (Fin n)))
    (ha : e a = i) (hc : e c = j) (hw : e w = k)
    (hA : e A = I) (hC : e C = J) (hW : e W = K) :
    ∀ x, x = a ∨ x = c ∨ x = w ∨ x = A ∨ x = C ∨ x = W := by
  intro x
  have hx : e x ∈ (↑(tripleSupport i j k ∪ tripleSupport I J K) : Set (Fin n)) :=
    he ▸ Set.mem_range_self x
  have hx' : e x = e a ∨ e x = e c ∨ e x = e w ∨
      e x = e A ∨ e x = e C ∨ e x = e W := by
    simpa [tripleSupport,ha,hc,hw,hA,hC,hW,or_assoc,or_comm,or_left_comm] using hx
  rcases hx' with h | h | h | h | h | h
  · exact Or.inl (e.injective h)
  · exact Or.inr (Or.inl (e.injective h))
  · exact Or.inr (Or.inr (Or.inl (e.injective h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (e.injective h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (e.injective h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (e.injective h)))))

theorem overlap_join {n} {b : Fin n → Nat} (hb : Monotone b)
    (P : Placement n) (hp : Valid b P) {i j k I J K : Fin n}
    (h1 : Legal b P i j k) (h2 : Legal b P I J K)
    (hj : FullJoin (tripleSupport i j k ∪ tripleSupport I J K).card) :
    ∃ z, Reach b (exchange P i j) z ∧ Reach b (exchange P I J) z := by
  obtain ⟨e,v,q,d,a,c,w,A,C,W,ha,hd,ht,hv,he,hea,hec,hew,heA,heC,heW,hl1,hl2⟩ :=
    compress_peak hb P hp h1 h2
  have hc := preimages_cover e i j k I J K a c w A C W he hea hec hew heA heC heW
  obtain ⟨z,hz1,hz2⟩ := hj d hd q hv a c w A C W hl1 hl2 hc
  have hpa : Agrees e v (exchange P i j) (exchange q a c) := by
    simpa only [hea,hec] using exchange_agrees e v ha a c
  have hpc : Agrees e v (exchange P I J) (exchange q A C) := by
    simpa only [heA,heC] using exchange_agrees e v ha A C
  apply lift_join hb e v ht (valid_exchange hb hp h1) (valid_exchange hb hp h2)
    hpa hpc ?_ hz1 hz2
  intro x hx
  rw [exchange_outside P i j x (by simpa only [hea] using hx a)
    (by simpa only [hec] using hx c),
    exchange_outside P I J x (by simpa only [heA] using hx A)
    (by simpa only [heC] using hx C)]

theorem legal_join {n} {b : Fin n → Nat} (hb : Monotone b)
    (p : Placement n) (hp : Valid b p) {i j k I J K : Fin n}
    (h1 : Legal b p i j k) (h2 : Legal b p I J K) :
    ∃ z, Reach b (exchange p i j) z ∧ Reach b (exchange p I J) z := by
  rcases tripleSupport_cases h1.1 h1.2.1 h2.1 h2.2.1 with he | hd | h4 | h5
  · rcases he with ⟨rfl,rfl,rfl⟩
    exact ⟨exchange p i j,.refl,.refl⟩
  · obtain ⟨z,hz1,hz2⟩ := disjoint_join hb hp h1 h2 hd
    exact ⟨z,Relation.ReflTransGen.single hz1,Relation.ReflTransGen.single hz2⟩
  · apply overlap_join hb p hp h1 h2
    rw [h4]; exact full_join4
  · apply overlap_join hb p hp h1 h2
    rw [h5]; exact full_join5

theorem local_confluence {n} {b : Fin n → Nat} (hb : Monotone b)
    {p q r : Placement n} (hq : Step b p q) (hr : Step b p r) :
    ∃ z, Reach b q z ∧ Reach b r z := by
  rcases hq with ⟨hp,i,j,k,h1,rfl⟩
  rcases hr with ⟨_,I,J,K,h2,rfl⟩
  exact legal_join hb p hp h1 h2
end Young213
```

```lean module=YoungLifting.lean
import YoungModel
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Relation

namespace Young213
open Finset

/-- Selected columns and selected row VALUES are both strictly ordered. -/
def Agrees {m n} (e v : Fin m ↪o Fin n) (P : Placement n) (q : Placement m) : Prop :=
  ∀ t, P (e t) = v (q t)

theorem swap_embed {m n} (e : Fin m ↪o Fin n) (i j x : Fin m) :
    Equiv.swap (e i) (e j) (e x) = e (Equiv.swap i j x) := by
  by_cases hi : x = i
  · subst x; simp
  by_cases hj : x = j
  · subst x; simp
  · simp [Equiv.swap_apply_of_ne_of_ne hi hj,
      Equiv.swap_apply_of_ne_of_ne (fun h => hi (e.injective h)) (fun h => hj (e.injective h))]

theorem exchange_agrees {m n} (e v : Fin m ↪o Fin n)
    {P : Placement n} {q : Placement m} (h : Agrees e v P q) (i j : Fin m) :
    Agrees e v (exchange P (e i) (e j)) (exchange q i j) := by
  intro t
  simp only [exchange_apply, swap_embed]
  exact h _

theorem exchange_outside {n} (P : Placement n) (i j x : Fin n)
    (hi : x ≠ i) (hj : x ≠ j) : exchange P i j x = P x := by
  simp [Equiv.swap_apply_of_ne_of_ne hi hj]

/-- Fixed thresholds compare EVERY selected row, independently of current witnesses. -/
def Thresholds {m n} (b : Fin n → Nat) (e v : Fin m ↪o Fin n)
    (d : Fin m → Nat) : Prop := ∀ i r, b (e i) ≤ (v r).val ↔ d i ≤ r.val

theorem legal_compression {m n} {b : Fin n → Nat} (e v : Fin m ↪o Fin n)
    {d : Fin m → Nat} (ht : Thresholds b e v d)
    {P : Placement n} {q : Placement m} (ha : Agrees e v P q) (i j k : Fin m) :
    Legal b P (e i) (e j) (e k) ↔ Legal d q i j k := by
  change ∀ t, P (e t) = v (q t) at ha
  change ∀ i r, b (e i) ≤ (v r).val ↔ d i ≤ r.val at ht
  simp only [Legal, ha, ht, OrderEmbedding.lt_iff_lt]

def Reach {n} (b : Fin n → Nat) := Relation.ReflTransGen (Step b)

theorem lift_step {m n} {b : Fin n → Nat} (hb : Monotone b)
    (e v : Fin m ↪o Fin n) {d : Fin m → Nat} (ht : Thresholds b e v d)
    {P : Placement n} {q r : Placement m} (hp : Valid b P)
    (ha : Agrees e v P q) (hs : Step d q r) :
    ∃ R, Step b P R ∧ Valid b R ∧ Agrees e v R r ∧
      ∀ x, (∀ t, x ≠ e t) → R x = P x := by
  rcases hs with ⟨_, i,j,k,hl,rfl⟩
  have hL := (legal_compression e v ht ha i j k).mpr hl
  refine ⟨exchange P (e i) (e j), ⟨hp,i |> e,j |> e,k |> e,hL,rfl⟩,
    valid_exchange hb hp hL, exchange_agrees e v ha i j, ?_⟩
  intro x hx
  exact exchange_outside P _ _ x (hx i) (hx j)

/-- Every finite compressed path lifts; rows and thresholds remain fixed for its entirety. -/
theorem lift_path {m n} {b : Fin n → Nat} (hb : Monotone b)
    (e v : Fin m ↪o Fin n) {d : Fin m → Nat} (ht : Thresholds b e v d)
    {q r : Placement m} (h : Reach d q r) :
    ∀ P, Valid b P → Agrees e v P q →
    ∃ R, Reach b P R ∧ Valid b R ∧ Agrees e v R r ∧
      ∀ x, (∀ t, x ≠ e t) → R x = P x := by
  induction h with
  | refl =>
    intro P hp ha
    exact ⟨P, .refl, hp, ha, fun _ _ => rfl⟩
  | @tail r s h hs ih =>
    intro P hp ha
    obtain ⟨R, hr, hv, haR, hout⟩ := ih P hp ha
    obtain ⟨S, hs', hvS, haS, houtS⟩ := lift_step hb e v ht hv haR hs
    exact ⟨S, hr.tail hs', hvS, haS, fun x hx => (houtS x hx).trans (hout x hx)⟩

/-- The set of row ranks that fit a selected column. -/
def fitting {m n} (b : Fin n → Nat) (e v : Fin m ↪o Fin n) (i : Fin m) : Finset (Fin m) :=
  univ.filter (fun r => b (e i) ≤ (v r).val)

 theorem fitting_nonempty {m n} {b : Fin n → Nat} {e v : Fin m ↪o Fin n}
    {P : Placement n} {q : Placement m} (hp : Valid b P) (ha : Agrees e v P q)
    (i : Fin m) : (fitting b e v i).Nonempty := by
  refine ⟨q i, ?_⟩
  simp only [fitting, mem_filter, mem_univ, true_and]
  rw [← ha i]
  exact hp (e i)

noncomputable def threshold {m n} {b : Fin n → Nat} {e v : Fin m ↪o Fin n}
    {P : Placement n} {q : Placement m} (hp : Valid b P) (ha : Agrees e v P q)
    (i : Fin m) : Nat := ((fitting b e v i).min' (fitting_nonempty hp ha i)).val

 theorem threshold_spec {m n} {b : Fin n → Nat} {e v : Fin m ↪o Fin n}
    {P : Placement n} {q : Placement m} (hp : Valid b P) (ha : Agrees e v P q) :
    Thresholds b e v (threshold hp ha) := by
  intro i r
  let s := fitting b e v i
  have hn : s.Nonempty := fitting_nonempty hp ha i
  change b (e i) ≤ (v r).val ↔ (s.min' hn).val ≤ r.val
  constructor
  · intro hr
    exact Finset.min'_le s r (by simpa [s, fitting] using hr)
  · intro hr
    have hm := Finset.min'_mem s hn
    have hfit : b (e i) ≤ (v (s.min' hn)).val := by simpa [s, fitting] using hm
    exact le_trans hfit (v.monotone hr)

 theorem threshold_monotone {m n} {b : Fin n → Nat} (hb : Monotone b)
    {e v : Fin m ↪o Fin n} {P : Placement n} {q : Placement m}
    (hp : Valid b P) (ha : Agrees e v P q) : Monotone (threshold hp ha) := by
  intro i j hij
  let r := (fitting b e v j).min' (fitting_nonempty hp ha j)
  have hr : b (e j) ≤ (v r).val := by
    have h := Finset.min'_mem (fitting b e v j) (fitting_nonempty hp ha j)
    simpa [fitting, r] using h
  exact (threshold_spec hp ha i r).mp (le_trans (hb (e.monotone hij)) hr)

end Young213
```

```lean module=YoungModel.lean
import Mathlib.Order.Fin.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Order.Hom.Basic
import Lean.Elab.Tactic.Omega

/- Candidate partial formalization of MathDB 380054. No confluence claim. -/
namespace Young213
abbrev Placement (n : Nat) := Equiv.Perm (Fin n)
def Valid {n} (b : Fin n → Nat) (p : Placement n) : Prop :=
  ∀ i, b i ≤ (p i).val
def Legal {n} (b : Fin n → Nat) (p : Placement n) (i j k : Fin n) : Prop :=
  i < j ∧ j < k ∧ b k ≤ (p j).val ∧ p j < p i ∧ p i < p k

def exchange {n} (p : Placement n) (i j : Fin n) : Placement n :=
  (Equiv.swap i j).trans p

@[simp] theorem exchange_apply {n} (p : Placement n) (i j x : Fin n) :
    exchange p i j x = p (Equiv.swap i j x) := rfl

def Step {n} (b : Fin n → Nat) (p q : Placement n) : Prop :=
  Valid b p ∧ ∃ i j k, Legal b p i j k ∧ q = exchange p i j

def Avoid213 {n} (b : Fin n → Nat) (p : Placement n) : Prop :=
  ¬ ∃ i j k, Legal b p i j k

def Terminal {n} (b : Fin n → Nat) (p : Placement n) : Prop :=
  ¬ ∃ q, Step b p q

/-- Every selected row meets every selected column, not merely its own dot. -/
def Rectangle {n} (b : Fin n → Nat) (p : Placement n) (i j k : Fin n) : Prop :=
  ∀ c, (c = i ∨ c = j ∨ c = k) →
    ∀ r, (r = i ∨ r = j ∨ r = k) → b c ≤ (p r).val

def SourceOccurrence {n} (b : Fin n → Nat) (p : Placement n) (i j k : Fin n) : Prop :=
  i < j ∧ j < k ∧ p j < p i ∧ p i < p k ∧ Rectangle b p i j k

theorem occurrence_iff {n} {b : Fin n → Nat} (hb : Monotone b)
    (p : Placement n) (i j k : Fin n) :
    SourceOccurrence b p i j k ↔ Legal b p i j k := by
  constructor
  · rintro ⟨hij, hjk, hji, hik, hr⟩
    exact ⟨hij, hjk, hr k (Or.inr (Or.inr rfl)) j (Or.inr (Or.inl rfl)), hji, hik⟩
  · rintro ⟨hij, hjk, hbk, hji, hik⟩
    refine ⟨hij, hjk, hji, hik, ?_⟩
    intro c hc r hr
    have hc' : c ≤ k := by rcases hc with rfl | rfl | rfl <;> omega
    have hr' : (p j).val ≤ (p r).val := by
      rcases hr with rfl | rfl | rfl <;> omega
    exact le_trans (hb hc') (le_trans hbk hr')

theorem valid_exchange {n} {b : Fin n → Nat} (hb : Monotone b)
    {p : Placement n} (hp : Valid b p) {i j k : Fin n} (h : Legal b p i j k) :
    Valid b (exchange p i j) := by
  rcases h with ⟨hij, hjk, hbk, hji, _⟩
  intro x
  by_cases hi : x = i
  · subst x
    simpa using le_trans (hb (le_of_lt (lt_trans hij hjk))) hbk
  by_cases hj : x = j
  · subst x
    have h : b j ≤ (p i).val := le_trans (le_trans (hb (le_of_lt hjk)) hbk) (le_of_lt hji)
    simpa using h
  · simpa [exchange, Equiv.swap_apply_of_ne_of_ne hi hj] using hp x

theorem step_valid {n} {b : Fin n → Nat} (hb : Monotone b)
    {p q : Placement n} (h : Step b p q) : Valid b q := by
  rcases h with ⟨hp, i, j, k, h, rfl⟩
  exact valid_exchange hb hp h

theorem terminal_iff_avoid {n} {b : Fin n → Nat} {p : Placement n}
    (hp : Valid b p) : Terminal b p ↔ Avoid213 b p := by
  constructor
  · intro h he
    rcases he with ⟨i,j,k,hl⟩
    exact h ⟨exchange p i j, hp, i,j,k,hl,rfl⟩
  · intro h he
    rcases he with ⟨q, _, i,j,k,hl,_⟩
    exact h ⟨i,j,k,hl⟩

/-- The greatest monotone minorant of caps, specified without computing minima. -/
def BelowSuffix {n} (h : Fin n → Nat) (i : Fin n) (a : Nat) : Prop :=
  ∀ t, i ≤ t → a ≤ h t

theorem monotone_below_caps_iff {n} {d h : Fin n → Nat} (hd : Monotone d) :
    (∀ i, d i ≤ h i) ↔ ∀ i, BelowSuffix h i (d i) := by
  constructor
  · intro H i t hit
    exact le_trans (hd hit) (H t)
  · intro H i
    exact H i i le_rfl

end Young213
```

```lean module=YoungPartition.lean
import YoungGlobal
namespace Young213
open Finset

/-- Top-left row lengths; zero and empty rows are allowed. -/
structure RowShape (n : Nat) where
  rows : Fin n → Nat
  decreasing : Antitone rows
  bounded : ∀ r, rows r ≤ n

def RowShape.Cell {n} (Y : RowShape n) (c r : Fin n) : Prop :=
  c.val < Y.rows (Fin.rev r)

def RowShape.columnRows {n} (Y : RowShape n) (c : Fin n) : Finset (Fin n) :=
  univ.filter (fun r => c.val < Y.rows (Fin.rev r))

noncomputable def RowShape.boundary {n} (Y : RowShape n) (c : Fin n) : Nat :=
  if h : (Y.columnRows c).Nonempty then ((Y.columnRows c).min' h).val else n

theorem RowShape.boundary_cell {n} (Y : RowShape n) (c r : Fin n) :
    Y.boundary c ≤ r.val ↔ Y.Cell c r := by
  classical
  unfold RowShape.boundary
  split_ifs with h
  · constructor
    · intro hr
      have hm := min'_mem (Y.columnRows c) h
      have hc : c.val < Y.rows (Fin.rev ((Y.columnRows c).min' h)) :=
        (mem_filter.mp hm).2
      exact lt_of_lt_of_le hc (Y.decreasing (Fin.rev_le_rev.mpr hr))
    · intro hc
      change (Y.columnRows c).min' h ≤ r
      apply min'_le (Y.columnRows c) r
      exact mem_filter.mpr ⟨mem_univ _,hc⟩
  · constructor
    · intro hr; omega
    · intro hc
      exact (h ⟨r,mem_filter.mpr ⟨mem_univ _,hc⟩⟩).elim

theorem RowShape.boundary_monotone {n} (Y : RowShape n) : Monotone Y.boundary := by
  classical
  intro c d hcd
  by_cases h : (Y.columnRows d).Nonempty
  · let r := (Y.columnRows d).min' h
    have hd : Y.Cell d r := (mem_filter.mp (min'_mem (Y.columnRows d) h)).2
    have hc : Y.Cell c r := lt_of_le_of_lt hcd hd
    have hl := (Y.boundary_cell c r).mpr hc
    simpa [RowShape.boundary,h,r] using hl
  · have hb : Y.boundary c ≤ n := by
      unfold RowShape.boundary
      split_ifs with hc
      · exact Nat.le_of_lt ((Y.columnRows c).min' hc).isLt
      · exact le_rfl
    simpa [RowShape.boundary,h] using hb

/-- The paper's staircase criterion, in top-left row indices. -/
def RowShape.Proper {n} (Y : RowShape n) : Prop := ∀ r, n - r.val ≤ Y.rows r

theorem RowShape.proper_iff {n} (Y : RowShape n) :
    Y.Proper ↔ ∀ c, Y.boundary c ≤ c.val := by
  constructor
  · intro hp c
    apply (Y.boundary_cell c c).mpr
    have h := hp (Fin.rev c)
    change c.val < Y.rows (Fin.rev c)
    simp only [Fin.val_rev] at h
    omega
  · intro hp r
    have h := (Y.boundary_cell (Fin.rev r) (Fin.rev r)).mp (hp (Fin.rev r))
    change (Fin.rev r).val < Y.rows (Fin.rev (Fin.rev r)) at h
    simp only [Fin.rev_rev,Fin.val_rev] at h
    omega

/-- One-based bottom-left coordinates and top-left partition indices agree. -/
theorem RowShape.coordinates {n} (Y : RowShape n) (c r : Fin n) :
    Y.Cell c r ↔ c.val + 1 ≤ Y.rows ⟨n - (r.val + 1), by omega⟩ := by
  have he : Fin.rev r = (⟨n - (r.val + 1), by omega⟩ : Fin n) := by
    apply Fin.ext; simp only [Fin.val_rev]
  simp only [RowShape.Cell,he]
  omega

def RowShape.Transversal {n} (Y : RowShape n) (D : Dots n) : Prop :=
  (∀ c r, D c r → Y.Cell c r) ∧
  (∀ c, ∃! r, D c r) ∧ (∀ r, ∃! c, D c r)

theorem RowShape.transversal_iff {n} (Y : RowShape n) (D : Dots n) :
    Y.Transversal D ↔ DotTransversal Y.boundary D := by
  simp only [RowShape.Transversal,DotTransversal,Y.boundary_cell]

def RowShape.Occurrence {n} (Y : RowShape n) (D : Dots n) (i j k : Fin n) : Prop :=
  ∃ a c w, D i a ∧ D j c ∧ D k w ∧ i < j ∧ j < k ∧ c < a ∧ a < w ∧
    ∀ x, (x = i ∨ x = j ∨ x = k) →
      ∀ r, (r = a ∨ r = c ∨ r = w) → Y.Cell x r

theorem RowShape.occurrence_iff {n} (Y : RowShape n) (D : Dots n) (i j k : Fin n) :
    Y.Occurrence D i j k ↔ DotOccurrence Y.boundary D i j k := by
  simp only [RowShape.Occurrence,DotOccurrence,Y.boundary_cell]

def RowShape.Move {n} (Y : RowShape n) (D E : Dots n) : Prop :=
  Y.Transversal D ∧ ∃ i j k, Y.Occurrence D i j k ∧
    ∀ x r, E x r ↔ D (Equiv.swap i j x) r

theorem RowShape.move_iff {n} (Y : RowShape n) (D E : Dots n) :
    Y.Move D E ↔ DotStep Y.boundary D E := by
  simp only [RowShape.Move,DotStep,Y.transversal_iff,Y.occurrence_iff]

abbrev RowShape.Paths {n} (Y : RowShape n) := Relation.ReflTransGen Y.Move
def RowShape.Avoids {n} (Y : RowShape n) (D : Dots n) : Prop :=
  ¬ ∃ i j k, Y.Occurrence D i j k

theorem RowShape.paths_iff {n} (Y : RowShape n) (D E : Dots n) :
    Y.Paths D E ↔ DotReach Y.boundary D E := by
  have he : Y.Move = DotStep Y.boundary := by
    funext D E; exact propext (Y.move_iff D E)
  rw [RowShape.Paths,he]; rfl

theorem RowShape.graph_avoids {n} (Y : RowShape n) (p : Placement n) :
    Y.Avoids (graph p) ↔ Avoid213 Y.boundary p := by
  simp only [RowShape.Avoids,Avoid213,Y.occurrence_iff,graph_occurrence,
    Young213.occurrence_iff Y.boundary_monotone]

theorem RowShape.unique_endpoint {n} (Y : RowShape n) (D : Dots n)
    (hD : Y.Transversal D) :
    ∃! E, Y.Paths D E ∧ Y.Transversal E ∧ Y.Avoids E := by
  obtain ⟨p,⟨hp,hg⟩,_⟩ := transversal_encoding ((Y.transversal_iff D).mp hD)
  subst D
  obtain ⟨t,⟨ht,hv,ha⟩,_⟩ := unique_normal_form Y.boundary_monotone p hp
  refine ⟨graph t,⟨(Y.paths_iff _ _).mpr ((source_path_iff Y.boundary_monotone p t).mpr ht),
    (Y.transversal_iff _).mpr ((graph_transversal t).mpr hv),
    (Y.graph_avoids t).mpr ha⟩,?_⟩
  intro E hE
  obtain ⟨q,hq,rfl⟩ := source_path_extract Y.boundary_monotone ((Y.paths_iff _ _).mp hE.1)
  have he := avoiding_unique Y.boundary_monotone p hp q t hq ht
    ((Y.graph_avoids q).mp hE.2.2) ha
  exact congrArg graph he
end Young213
```

```lean module=YoungPeaks.lean
import YoungLifting

namespace Young213
open Finset

/-- Suffix minimum: the strongest nondecreasing boundary under a cap vector. -/
noncomputable def suffixCap {n} (h : Fin n → Nat) (i : Fin n) : Nat :=
  ((univ.filter (fun t : Fin n => i ≤ t)).image h).min'
    ⟨h i, mem_image.mpr ⟨i, by simp, rfl⟩⟩

theorem suffixCap_le {n} (h : Fin n → Nat) (i t : Fin n) (hit : i ≤ t) :
    suffixCap h i ≤ h t := by
  apply min'_le
  exact mem_image.mpr ⟨t, by simp [hit], rfl⟩

theorem le_suffixCap {n} (h : Fin n → Nat) (i : Fin n) (a : Nat)
    (ha : ∀ t, i ≤ t → a ≤ h t) : a ≤ suffixCap h i := by
  apply le_min'
  intro y hy
  obtain ⟨t,ht,rfl⟩ := mem_image.mp hy
  exact ha t (mem_filter.mp ht).2

theorem suffixCap_monotone {n} (h : Fin n → Nat) : Monotone (suffixCap h) := by
  intro i j hij
  apply le_suffixCap
  intro t hjt
  exact suffixCap_le h i t (le_trans hij hjt)

theorem suffixCap_greatest {n} (h d : Fin n → Nat) (hd : Monotone d) :
    (∀ i, d i ≤ h i) ↔ ∀ i, d i ≤ suffixCap h i := by
  constructor
  · intro H i
    apply le_suffixCap
    intro t hit
    exact le_trans (hd hit) (H t)
  · intro H i
    exact le_trans (H i) (suffixCap_le h i i le_rfl)

/-- Two full-triple legality constraints, including caps at both witnesses. -/
def peakCaps {n} (p : Placement n) (j k J K : Fin n) (t : Fin n) : Nat :=
  min (p t).val (min (if t = k then (p j).val else (p t).val)
    (if t = K then (p J).val else (p t).val))

 theorem peakCaps_iff {n} (p : Placement n) (d : Fin n → Nat) (j k J K : Fin n) :
    (∀ t, d t ≤ peakCaps p j k J K t) ↔
    Valid d p ∧ d k ≤ (p j).val ∧ d K ≤ (p J).val := by
  constructor
  · intro H
    refine ⟨fun t => le_trans (H t) (min_le_left _ _), ?_, ?_⟩
    · have h := le_trans (H k) (le_trans (min_le_right _ _) (min_le_left _ _))
      simpa using h
    · have h := le_trans (H K) (le_trans (min_le_right _ _) (min_le_right _ _))
      simpa using h
  · rintro ⟨hp,hk,hK⟩ t
    apply le_min (hp t)
    apply le_min
    · split_ifs with h
      · subst t; exact hk
      · exact hp t
    · split_ifs with h
      · subst t; exact hK
      · exact hp t

 theorem strongest_boundary {n} (p : Placement n) (d : Fin n → Nat)
    (hd : Monotone d) (j k J K : Fin n) :
    (Valid d p ∧ d k ≤ (p j).val ∧ d K ≤ (p J).val) ↔
    ∀ t, d t ≤ suffixCap (peakCaps p j k J K) t := by
  rw [← peakCaps_iff, suffixCap_greatest _ _ hd]

 theorem step_boundary_mono {n} {d B : Fin n → Nat} (hd : ∀ i, d i ≤ B i)
    {p q : Placement n} (h : Step B p q) : Step d p q := by
  rcases h with ⟨hp,i,j,k,hl,rfl⟩
  rcases hl with ⟨hij,hjk,hb,hji,hik⟩
  exact ⟨fun x => le_trans (hd x) (hp x),i,j,k,⟨hij,hjk,le_trans (hd k) hb,hji,hik⟩,rfl⟩

 theorem reach_boundary_mono {n} {d B : Fin n → Nat} (hd : ∀ i, d i ≤ B i)
    {p q : Placement n} (h : Reach B p q) : Reach d p q := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (step_boundary_mono hd hs)

 theorem exchange_commute {n} (p : Placement n) (i j I J : Fin n)
    (hiI : i ≠ I) (hiJ : i ≠ J) (hjI : j ≠ I) (hjJ : j ≠ J) :
    exchange (exchange p i j) I J = exchange (exchange p I J) i j := by
  ext x
  by_cases hxi : x = i
  · subst x; simp [Equiv.swap_apply_def, hiI, hiJ, hjI, hjJ]
  by_cases hxj : x = j
  · subst x; simp [Equiv.swap_apply_def, hiI, hiJ, hjI, hjJ]
  by_cases hxI : x = I
  · subst x; simp [Equiv.swap_apply_def, Ne.symm hiI, Ne.symm hjI, Ne.symm hiJ, Ne.symm hjJ]
  by_cases hxJ : x = J
  · subst x; simp [Equiv.swap_apply_def, Ne.symm hiI, Ne.symm hjI, Ne.symm hiJ, Ne.symm hjJ]
  · simp [Equiv.swap_apply_def, hxi, hxj, hxI, hxJ]


 theorem strongest_admissible {n} (p : Placement n) (j k J K : Fin n) :
    Monotone (suffixCap (peakCaps p j k J K)) ∧
    Valid (suffixCap (peakCaps p j k J K)) p ∧
    suffixCap (peakCaps p j k J K) k ≤ (p j).val ∧
    suffixCap (peakCaps p j k J K) K ≤ (p J).val := by
  refine ⟨suffixCap_monotone _, ?_⟩
  apply (peakCaps_iff p _ j k J K).mp
  intro t
  exact suffixCap_le _ t t le_rfl

def DisjointTriples {n} (i j k I J K : Fin n) : Prop :=
  ∀ x, (x = i ∨ x = j ∨ x = k) →
    ∀ y, (y = I ∨ y = J ∨ y = K) → x ≠ y

 theorem disjoint_legal {n} {b : Fin n → Nat} {p : Placement n}
    {i j k I J K : Fin n} (hd : DisjointTriples i j k I J K)
    (hc : Legal b p I J K) : Legal b (exchange p i j) I J K := by
  have hI := hd i (Or.inl rfl) I (Or.inl rfl)
  have hI' := hd j (Or.inr (Or.inl rfl)) I (Or.inl rfl)
  have hJ := hd i (Or.inl rfl) J (Or.inr (Or.inl rfl))
  have hJ' := hd j (Or.inr (Or.inl rfl)) J (Or.inr (Or.inl rfl))
  have hK := hd i (Or.inl rfl) K (Or.inr (Or.inr rfl))
  have hK' := hd j (Or.inr (Or.inl rfl)) K (Or.inr (Or.inr rfl))
  unfold Legal
  rw [exchange_outside p i j I hI.symm hI'.symm,
    exchange_outside p i j J hJ.symm hJ'.symm,
    exchange_outside p i j K hK.symm hK'.symm]
  exact hc

 theorem disjoint_join {n} {b : Fin n → Nat} (hb : Monotone b)
    {p : Placement n} (hp : Valid b p) {i j k I J K : Fin n}
    (ha : Legal b p i j k) (hc : Legal b p I J K)
    (hd : DisjointTriples i j k I J K) :
    ∃ z, Step b (exchange p i j) z ∧ Step b (exchange p I J) z := by
  have hd' : DisjointTriples I J K i j k := by
    intro x hx y hy
    exact (hd y hy x hx).symm
  have he := exchange_commute p i j I J
    (hd i (Or.inl rfl) I (Or.inl rfl))
    (hd i (Or.inl rfl) J (Or.inr (Or.inl rfl)))
    (hd j (Or.inr (Or.inl rfl)) I (Or.inl rfl))
    (hd j (Or.inr (Or.inl rfl)) J (Or.inr (Or.inl rfl)))
  exact ⟨exchange (exchange p i j) I J,
    ⟨valid_exchange hb hp ha,I,J,K,disjoint_legal hd hc,rfl⟩,
    ⟨valid_exchange hb hp hc,i,j,k,disjoint_legal hd' ha,he⟩⟩

end Young213
```

```lean module=YoungSequences.lean
import YoungEndpoint
namespace Young213

theorem peakCaps_symm {n} (p : Placement n) (j k J K : Fin n) :
    peakCaps p j k J K = peakCaps p J K j k := by
  funext t
  simp only [peakCaps,min_comm]

theorem strongest_symm {n} (p : Placement n) (j k J K : Fin n) :
    suffixCap (peakCaps p j k J K) = suffixCap (peakCaps p J K j k) := by
  rw [peakCaps_symm p j k J K]

theorem path_sequence {α : Type*} {R : α → α → Prop} {p q : α}
    (h : Relation.ReflTransGen R p q) :
    ∃ (length : Nat) (f : Nat → α), f 0 = p ∧ f length = q ∧
      ∀ t, t < length → R (f t) (f (t+1)) := by
  classical
  induction h with
  | refl => exact ⟨0,fun _ => p,rfl,rfl,fun t ht => (by omega)⟩
  | @tail q z h hs ih =>
    obtain ⟨l,f,h0,hl,hf⟩ := ih
    let g : Nat → α := fun t => if t ≤ l then f t else z
    refine ⟨l+1,g,?_,?_,?_⟩
    · simpa only [g,ite_eq_left (Nat.zero_le l)] using h0
    · simp only [g,show ¬ l+1 ≤ l by omega,ite_false]
    · intro t ht
      by_cases htl : t < l
      · simpa only [g,ite_eq_left (show t ≤ l by omega),
          ite_eq_left (show t+1 ≤ l by omega)] using hf t htl
      · have he : t = l := by omega
        subst t
        simpa only [g,ite_eq_left le_rfl,show ¬ l+1 ≤ l by omega,ite_false,hl] using hs

theorem source_shape_complete {n} (Y : RowShape n) (D : Dots n) (hD : Y.Transversal D) :
    (∀ E F, Y.Paths D E → Y.Paths D F → ∃ G, Y.Paths E G ∧ Y.Paths F G) ∧
    (∀ f : Nat → Dots n, (∀ t, Y.Move (f t) (f (t+1))) → False) ∧
    ∃ E, (Y.Paths D E ∧ Y.Transversal E ∧ Y.Avoids E) ∧
      (∀ F, Y.Paths D F → Y.Avoids F → F = E) ∧
      (∃ length f, Y.Maximal D length f ∧ f length = E) ∧
      (∀ length f, Y.Maximal D length f → f length = E) := by
  obtain ⟨hu,hi,E,hr,hv,ha,hm⟩ := source_shape_endpoint Y D hD
  obtain ⟨length,f,h0,hend,hsteps⟩ := path_sequence hr
  refine ⟨fun _ _ => Y.confluence hD,hi,E,⟨hr,hv,ha⟩,?_,?_,hm⟩
  · intro F hF aF
    obtain ⟨E',hE',huniq⟩ := hu
    exact (huniq F ⟨hF,Y.paths_valid hD hF,aF⟩).trans
      (huniq E ⟨hr,hv,ha⟩).symm
  · refine ⟨length,f,⟨h0,hsteps,?_⟩,hend⟩
    rw [hend]
    exact (Y.terminal_iff_avoids hv).mpr ha
end Young213
```

```lean module=YoungSource.lean
import YoungTermination
import YoungPeaks

namespace Young213

abbrev Dots (n : Nat) := Fin n → Fin n → Prop
def graph {n} (p : Placement n) : Dots n := fun c r => p c = r

def DotTransversal {n} (b : Fin n → Nat) (D : Dots n) : Prop :=
  (∀ c r, D c r → b c ≤ r.val) ∧
  (∀ c, ∃! r, D c r) ∧ (∀ r, ∃! c, D c r)

 theorem graph_transversal {n} {b : Fin n → Nat} (p : Placement n) :
    DotTransversal b (graph p) ↔ Valid b p := by
  constructor
  · intro h c; exact h.1 c (p c) rfl
  · intro hp
    refine ⟨?_, ?_, ?_⟩
    · intro c r h; subst r; exact hp c
    · intro c; exact ⟨p c, rfl, fun _ h => h.symm⟩
    · intro r; exact ⟨p.symm r, p.apply_symm_apply r, fun c h => p.injective (h.trans (p.apply_symm_apply r).symm)⟩

/-- A literal dot arrangement is uniquely encoded by a valid permutation. -/
 theorem transversal_encoding {n} {b : Fin n → Nat} {D : Dots n}
    (hD : DotTransversal b D) : ∃! p : Placement n, Valid b p ∧ graph p = D := by
  classical
  let f : Fin n → Fin n := fun c => Classical.choose (ExistsUnique.exists (hD.2.1 c))
  have hf : ∀ c, D c (f c) := fun c => Classical.choose_spec (ExistsUnique.exists (hD.2.1 c))
  have hinj : Function.Injective f := by
    intro c c' he
    obtain ⟨d,_,hu⟩ := hD.2.2 (f c)
    exact (hu c (hf c)).trans (hu c' (he ▸ hf c')).symm
  have hsurj : Function.Surjective f := by
    intro r
    obtain ⟨c,hcr,_⟩ := hD.2.2 r
    obtain ⟨r',_,hu⟩ := hD.2.1 c
    exact ⟨c,(hu (f c) (hf c)).trans (hu r hcr).symm⟩
  let p : Placement n := Equiv.ofBijective f ⟨hinj,hsurj⟩
  have hgraph : graph p = D := by
    funext c r
    apply propext
    constructor
    · intro he
      exact he ▸ hf c
    · intro hcr
      obtain ⟨r',_,hu⟩ := hD.2.1 c
      exact (hu (f c) (hf c)).trans (hu r hcr).symm
  refine ⟨p, ⟨fun c => hD.1 c (p c) (hf c), hgraph⟩, ?_⟩
  intro q hq
  apply Equiv.ext
  intro c
  have h : graph q c (p c) := by rw [hq.2, ← hgraph]; rfl
  exact h

/-- Source occurrence: dots of relative order 213 and all nine intersections present. -/
def DotOccurrence {n} (b : Fin n → Nat) (D : Dots n) (i j k : Fin n) : Prop :=
  ∃ a c w, D i a ∧ D j c ∧ D k w ∧ i < j ∧ j < k ∧ c < a ∧ a < w ∧
    ∀ x, (x = i ∨ x = j ∨ x = k) →
      ∀ r, (r = a ∨ r = c ∨ r = w) → b x ≤ r.val

 theorem graph_occurrence {n} {b : Fin n → Nat} (p : Placement n) (i j k : Fin n) :
    DotOccurrence b (graph p) i j k ↔ SourceOccurrence b p i j k := by
  constructor
  · rintro ⟨a,c,w,ha,hc,hw,hij,hjk,hca,haw,hr⟩
    change p i = a at ha; change p j = c at hc; change p k = w at hw
    subst a; subst c; subst w
    refine ⟨hij,hjk,hca,haw,?_⟩
    intro x hx r hrr
    apply hr x hx (p r)
    rcases hrr with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro ⟨hij,hjk,hca,haw,hr⟩
    refine ⟨p i,p j,p k,rfl,rfl,rfl,hij,hjk,hca,haw,?_⟩
    intro x hx r hrr
    rcases hrr with rfl | rfl | rfl
    · exact hr x hx i (Or.inl rfl)
    · exact hr x hx j (Or.inr (Or.inl rfl))
    · exact hr x hx k (Or.inr (Or.inr rfl))

/-- The source swaps entire columns' dot values, retaining all other cells. -/
def DotStep {n} (b : Fin n → Nat) (D E : Dots n) : Prop :=
  DotTransversal b D ∧ ∃ i j k, DotOccurrence b D i j k ∧
    ∀ x r, E x r ↔ D (Equiv.swap i j x) r

 theorem source_step_iff {n} {b : Fin n → Nat} (hb : Monotone b)
    (p q : Placement n) : DotStep b (graph p) (graph q) ↔ Step b p q := by
  constructor
  · rintro ⟨hp,i,j,k,ho,he⟩
    refine ⟨(graph_transversal p).mp hp,i,j,k,
      (occurrence_iff hb p i j k).mp ((graph_occurrence p i j k).mp ho), ?_⟩
    apply Equiv.ext
    intro x
    exact (he x (exchange p i j x)).mpr rfl
  · rintro ⟨hp,i,j,k,ho,rfl⟩
    exact ⟨(graph_transversal p).mpr hp,i,j,k,
      (graph_occurrence p i j k).mpr ((occurrence_iff hb p i j k).mpr ho), fun _ _ => Iff.rfl⟩


def DotReach {n} (b : Fin n → Nat) := Relation.ReflTransGen (DotStep b)

 theorem source_step_extract {n} {b : Fin n → Nat} (hb : Monotone b)
    (p : Placement n) {E : Dots n} (h : DotStep b (graph p) E) :
    ∃ q, Step b p q ∧ E = graph q := by
  rcases h with ⟨hp,i,j,k,ho,he⟩
  refine ⟨exchange p i j, ?_, ?_⟩
  · exact ⟨(graph_transversal p).mp hp,i,j,k,
      (occurrence_iff hb p i j k).mp ((graph_occurrence p i j k).mp ho),rfl⟩
  · funext x r
    exact propext (he x r)

 theorem source_path_extract {n} {b : Fin n → Nat} (hb : Monotone b)
    {p : Placement n} {D : Dots n} (h : DotReach b (graph p) D) :
    ∃ q, Reach b p q ∧ D = graph q := by
  induction h with
  | refl => exact ⟨p,.refl,rfl⟩
  | tail _ hs ih =>
    obtain ⟨q,hq,rfl⟩ := ih
    obtain ⟨r,hr,rfl⟩ := source_step_extract hb q hs
    exact ⟨r,hq.tail hr,rfl⟩

 theorem source_path_iff {n} {b : Fin n → Nat} (hb : Monotone b)
    (p q : Placement n) : DotReach b (graph p) (graph q) ↔ Reach b p q := by
  constructor
  · intro h
    obtain ⟨r,hr,he⟩ := source_path_extract hb h
    have hqr : q = r := by
      apply Equiv.ext
      intro x
      have h : graph r x (q x) := by rw [← he]; rfl
      exact h.symm
    subst q
    exact hr
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hs ih => exact ih.tail ((source_step_iff hb _ _).mpr hs)

/-- Exact partial endpoint. Uniqueness and full confluence are deliberately absent. -/
theorem partial_endpoint {n} (b : Fin n → Nat) (hb : Monotone b) :
    WellFounded (fun q p : Placement n => Step b p q) ∧
    ∀ p, Valid b p → ∃ t, Reach b p t ∧ Valid b t ∧ Avoid213 b t :=
  ⟨terminating b,fun p hp => terminal_exists hb p hp⟩

end Young213
```

```lean module=YoungSupport.lean
import YoungSource
import Mathlib.Data.Finset.Sort

namespace Young213
open Finset

/-- Ordered compression exists for every selected support, with no size bound. -/
theorem ordered_support {n} (P : Placement n) (s : Finset (Fin n)) :
    ∃ (e v : Fin s.card ↪o Fin n) (q : Placement s.card),
      Set.range e = (s : Set (Fin n)) ∧
      Set.range v = (s.image P : Set (Fin n)) ∧ Agrees e v P q := by
  classical
  let r := s.image P
  have hc : r.card = s.card := Finset.card_image_of_injective s P.injective
  let E := s.orderIsoOfFin rfl
  let V := r.orderIsoOfFin hc
  let f : s → r := fun x => ⟨P x, mem_image.mpr ⟨x, x.property, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      exact P.injective (congrArg Subtype.val h)
    · intro y
      obtain ⟨x,hx,hxy⟩ := mem_image.mp y.property
      exact ⟨⟨x,hx⟩, Subtype.ext hxy⟩
  let F := Equiv.ofBijective f hf
  let q : Placement s.card := E.toEquiv.trans (F.trans V.symm.toEquiv)
  refine ⟨s.orderEmbOfFin rfl, r.orderEmbOfFin hc, q,
    s.range_orderEmbOfFin rfl, r.range_orderEmbOfFin hc, ?_⟩
  intro t
  change P (E t).val = (V (q t)).val
  have h : V (q t) = F (E t) := V.apply_symm_apply (F (E t))
  exact (congrArg Subtype.val h).symm

/-- Compression supplies the fixed threshold board needed by path lifting. -/
theorem compressed_support {n} {b : Fin n → Nat} (hb : Monotone b)
    (P : Placement n) (hp : Valid b P) (s : Finset (Fin n)) :
    ∃ (e v : Fin s.card ↪o Fin n) (q : Placement s.card) (d : Fin s.card → Nat),
      Set.range e = (s : Set (Fin n)) ∧
      Set.range v = (s.image P : Set (Fin n)) ∧
      Agrees e v P q ∧ Monotone d ∧ Thresholds b e v d ∧ Valid d q := by
  obtain ⟨e,v,q,he,hv,ha⟩ := ordered_support P s
  refine ⟨e,v,q,threshold hp ha,he,hv,ha,threshold_monotone hb hp ha,
    threshold_spec hp ha, ?_⟩
  intro i
  apply (threshold_spec hp ha i (q i)).mp
  rw [← ha i]
  exact hp (e i)

/-- Agreement on the selected columns and equality outside them determine a placement. -/
theorem agrees_ext {m n} {e v : Fin m ↪o Fin n} {q : Placement m}
    {P Q : Placement n} (hP : Agrees e v P q) (hQ : Agrees e v Q q)
    (hout : ∀ x, (∀ t, x ≠ e t) → P x = Q x) : P = Q := by
  classical
  apply Equiv.ext
  intro x
  by_cases hx : ∃ t, x = e t
  · obtain ⟨t,rfl⟩ := hx
    exact (hP t).trans (hQ t).symm
  · exact hout x (fun t h => hx ⟨t,h⟩)

/-- A compressed join lifts to an actual join, including equality outside the support. -/
theorem lift_join {m n} {b : Fin n → Nat} (hb : Monotone b)
    (e v : Fin m ↪o Fin n) {d : Fin m → Nat} (ht : Thresholds b e v d)
    {q r z : Placement m} {P Q : Placement n}
    (hp : Valid b P) (hq : Valid b Q) (ha : Agrees e v P q) (hc : Agrees e v Q r)
    (hout : ∀ x, (∀ t, x ≠ e t) → P x = Q x)
    (h1 : Reach d q z) (h2 : Reach d r z) :
    ∃ Z, Reach b P Z ∧ Reach b Q Z := by
  obtain ⟨A,hA,_,haA,hoA⟩ := lift_path hb e v ht h1 P hp ha
  obtain ⟨B,hB,_,haB,hoB⟩ := lift_path hb e v ht h2 Q hq hc
  have he : A = B := agrees_ext haA haB (fun x hx =>
    (hoA x hx).trans ((hout x hx).trans (hoB x hx).symm))
  exact ⟨A,hA,he ▸ hB⟩
end Young213
```

```lean module=YoungSupportPeaks.lean
import YoungSupport
namespace Young213
open Finset

def tripleSupport {n} (i j k : Fin n) : Finset (Fin n) := {i,j,k}

theorem tripleSupport_card {n} {i j k : Fin n} (hij : i < j) (hjk : j < k) :
    (tripleSupport i j k).card = 3 := by
  simp [tripleSupport, ne_of_lt hij, ne_of_lt hjk, ne_of_lt (lt_trans hij hjk)]

theorem tripleSupport_eq {n} {i j k I J K : Fin n}
    (hij : i < j) (hjk : j < k) (hIJ : I < J) (hJK : J < K)
    (h : tripleSupport i j k = tripleSupport I J K) : i = I ∧ j = J ∧ k = K := by
  have hi : i = I ∨ i = J ∨ i = K := by
    have : i ∈ tripleSupport I J K := h ▸ (by simp [tripleSupport])
    simpa [tripleSupport] using this
  have hI : I = i ∨ I = j ∨ I = k := by
    have : I ∈ tripleSupport i j k := h ▸ (by simp [tripleSupport])
    simpa [tripleSupport] using this
  have hk : k = I ∨ k = J ∨ k = K := by
    have : k ∈ tripleSupport I J K := h ▸ (by simp [tripleSupport])
    simpa [tripleSupport] using this
  have hK : K = i ∨ K = j ∨ K = k := by
    have : K ∈ tripleSupport i j k := h ▸ (by simp [tripleSupport])
    simpa [tripleSupport] using this
  have hj : j = I ∨ j = J ∨ j = K := by
    have : j ∈ tripleSupport I J K := h ▸ (by simp [tripleSupport])
    simpa [tripleSupport] using this
  omega

/-- Exhaustive support-size split, before any rank or join computation. -/
theorem tripleSupport_cases {n} {i j k I J K : Fin n}
    (hij : i < j) (hjk : j < k) (hIJ : I < J) (hJK : J < K) :
    (i = I ∧ j = J ∧ k = K) ∨ DisjointTriples i j k I J K ∨
    (tripleSupport i j k ∪ tripleSupport I J K).card = 4 ∨
    (tripleSupport i j k ∪ tripleSupport I J K).card = 5 := by
  let s := tripleSupport i j k
  let t := tripleSupport I J K
  have hs : s.card = 3 := tripleSupport_card hij hjk
  have ht : t.card = 3 := tripleSupport_card hIJ hJK
  have hlo := card_le_card (subset_union_left : s ⊆ s ∪ t)
  have hhi := card_union_le s t
  by_cases h3 : (s ∪ t).card = 3
  · have he : s = t := (eq_of_subset_of_card_le subset_union_left (by omega)).trans
        (eq_of_subset_of_card_le subset_union_right (by omega)).symm
    exact Or.inl (tripleSupport_eq hij hjk hIJ hJK he)
  by_cases h6 : (s ∪ t).card = 6
  · have hd : Disjoint s t := card_union_eq_card_add_card.mp (by omega)
    right; left
    intro x hx y hy hxy
    have hx' : x ∈ s := by simpa [s,tripleSupport] using hx
    have hy' : y ∈ t := by simpa [t,tripleSupport] using hy
    exact (Finset.disjoint_left.mp hd hx') (hxy ▸ hy')
  · right; right
    change (s ∪ t).card = 4 ∨ (s ∪ t).card = 5
    omega

/-- Every arbitrary pair of legal triples admits ranked compression on its full union. -/
theorem compress_peak {n} {b : Fin n → Nat} (hb : Monotone b)
    (P : Placement n) (hp : Valid b P) {i j k I J K : Fin n}
    (h1 : Legal b P i j k) (h2 : Legal b P I J K) :
    let s := tripleSupport i j k ∪ tripleSupport I J K
    ∃ (e v : Fin s.card ↪o Fin n) (q : Placement s.card) (d : Fin s.card → Nat)
      (a c w A C W : Fin s.card),
      Agrees e v P q ∧ Monotone d ∧ Thresholds b e v d ∧ Valid d q ∧
      Set.range e = (s : Set (Fin n)) ∧
      e a = i ∧ e c = j ∧ e w = k ∧ e A = I ∧ e C = J ∧ e W = K ∧
      Legal d q a c w ∧ Legal d q A C W := by
  dsimp only
  let s := tripleSupport i j k ∪ tripleSupport I J K
  obtain ⟨e,v,q,d,he,_,ha,hd,ht,hv⟩ := compressed_support hb P hp s
  have hi : i ∈ Set.range e := by rw [he]; simp [s,tripleSupport]
  have hj : j ∈ Set.range e := by rw [he]; simp [s,tripleSupport]
  have hk : k ∈ Set.range e := by rw [he]; simp [s,tripleSupport]
  have hI : I ∈ Set.range e := by rw [he]; simp [s,tripleSupport]
  have hJ : J ∈ Set.range e := by rw [he]; simp [s,tripleSupport]
  have hK : K ∈ Set.range e := by rw [he]; simp [s,tripleSupport]
  obtain ⟨a,hea⟩ := hi; obtain ⟨c,hec⟩ := hj; obtain ⟨w,hew⟩ := hk
  obtain ⟨A,heA⟩ := hI; obtain ⟨C,heC⟩ := hJ; obtain ⟨W,heW⟩ := hK
  exact ⟨e,v,q,d,a,c,w,A,C,W,ha,hd,ht,hv,he,hea,hec,hew,heA,heC,heW,
    (legal_compression e v ht ha a c w).mp (by simpa only [hea,hec,hew] using h1),
    (legal_compression e v ht ha A C W).mp (by simpa only [heA,heC,heW] using h2)⟩
end Young213
```

```lean module=YoungTableJoins.lean
import YoungCoverage
namespace Young213
theorem table_join4 (p : Placement 4) (t u : Fin 4 × Fin 4 × Fin 4)
    (h : ((p : Fin 4 → Fin 4), t, u) ∈ rankCases4) :
    ∃ z, Reach (suffixCap (peakCaps p t.2.1 t.2.2 u.2.1 u.2.2))
      (exchange p t.1 t.2.1) z ∧
      Reach (suffixCap (peakCaps p t.2.1 t.2.2 u.2.1 u.2.2))
      (exchange p u.1 u.2.1) z := by
  simp only [rankCases4, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h
  · have hf : (p : Fin 4 → Fin 4) = case1p := congrArg Prod.fst h
    have ht : t = (0,1,2) := congrArg (fun x => x.2.1) h
    have hu : u = (0,1,3) := congrArg (fun x => x.2.2) h
    have hp : p = case1p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case1_strongest]
    exact case1_join
  · have hf : (p : Fin 4 → Fin 4) = case2p := congrArg Prod.fst h
    have ht : t = (0,1,2) := congrArg (fun x => x.2.1) h
    have hu : u = (0,1,3) := congrArg (fun x => x.2.2) h
    have hp : p = case2p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case2_strongest]
    exact case2_join
  · have hf : (p : Fin 4 → Fin 4) = case3p := congrArg Prod.fst h
    have ht : t = (0,2,3) := congrArg (fun x => x.2.1) h
    have hu : u = (1,2,3) := congrArg (fun x => x.2.2) h
    have hp : p = case3p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case3_strongest]
    exact case3_join
  · have hf : (p : Fin 4 → Fin 4) = case4p := congrArg Prod.fst h
    have ht : t = (0,1,3) := congrArg (fun x => x.2.1) h
    have hu : u = (0,2,3) := congrArg (fun x => x.2.2) h
    have hp : p = case4p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case4_strongest]
    exact case4_join
  · have hf : (p : Fin 4 → Fin 4) = case5p := congrArg Prod.fst h
    have ht : t = (0,1,3) := congrArg (fun x => x.2.1) h
    have hu : u = (0,2,3) := congrArg (fun x => x.2.2) h
    have hp : p = case5p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case5_strongest]
    exact case5_join
  · have hf : (p : Fin 4 → Fin 4) = case6p := congrArg Prod.fst h
    have ht : t = (0,1,3) := congrArg (fun x => x.2.1) h
    have hu : u = (1,2,3) := congrArg (fun x => x.2.2) h
    have hp : p = case6p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case6_strongest]
    exact case6_join
  · have hf : (p : Fin 4 → Fin 4) = case7p := congrArg Prod.fst h
    have ht : t = (0,2,3) := congrArg (fun x => x.2.1) h
    have hu : u = (1,2,3) := congrArg (fun x => x.2.2) h
    have hp : p = case7p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case7_strongest]
    exact case7_join
theorem table_join5 (p : Placement 5) (t u : Fin 5 × Fin 5 × Fin 5)
    (h : ((p : Fin 5 → Fin 5), t, u) ∈ rankCases5) :
    ∃ z, Reach (suffixCap (peakCaps p t.2.1 t.2.2 u.2.1 u.2.2))
      (exchange p t.1 t.2.1) z ∧
      Reach (suffixCap (peakCaps p t.2.1 t.2.2 u.2.1 u.2.2))
      (exchange p u.1 u.2.1) z := by
  simp only [rankCases5, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have hf : (p : Fin 5 → Fin 5) = case8p := congrArg Prod.fst h
    have ht : t = (0,1,2) := congrArg (fun x => x.2.1) h
    have hu : u = (2,3,4) := congrArg (fun x => x.2.2) h
    have hp : p = case8p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case8_strongest]
    exact case8_join
  · have hf : (p : Fin 5 → Fin 5) = case9p := congrArg Prod.fst h
    have ht : t = (0,1,3) := congrArg (fun x => x.2.1) h
    have hu : u = (2,3,4) := congrArg (fun x => x.2.2) h
    have hp : p = case9p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case9_strongest]
    exact case9_join
  · have hf : (p : Fin 5 → Fin 5) = case10p := congrArg Prod.fst h
    have ht : t = (0,1,4) := congrArg (fun x => x.2.1) h
    have hu : u = (2,3,4) := congrArg (fun x => x.2.2) h
    have hp : p = case10p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case10_strongest]
    exact case10_join
  · have hf : (p : Fin 5 → Fin 5) = case11p := congrArg Prod.fst h
    have ht : t = (0,2,3) := congrArg (fun x => x.2.1) h
    have hu : u = (1,2,4) := congrArg (fun x => x.2.2) h
    have hp : p = case11p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case11_strongest]
    exact case11_join
  · have hf : (p : Fin 5 → Fin 5) = case12p := congrArg Prod.fst h
    have ht : t = (0,2,4) := congrArg (fun x => x.2.1) h
    have hu : u = (1,2,3) := congrArg (fun x => x.2.2) h
    have hp : p = case12p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case12_strongest]
    exact case12_join
  · have hf : (p : Fin 5 → Fin 5) = case13p := congrArg Prod.fst h
    have ht : t = (0,2,3) := congrArg (fun x => x.2.1) h
    have hu : u = (1,2,4) := congrArg (fun x => x.2.2) h
    have hp : p = case13p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case13_strongest]
    exact case13_join
  · have hf : (p : Fin 5 → Fin 5) = case14p := congrArg Prod.fst h
    have ht : t = (0,2,4) := congrArg (fun x => x.2.1) h
    have hu : u = (1,2,3) := congrArg (fun x => x.2.2) h
    have hp : p = case14p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case14_strongest]
    exact case14_join
  · have hf : (p : Fin 5 → Fin 5) = case15p := congrArg Prod.fst h
    have ht : t = (0,2,3) := congrArg (fun x => x.2.1) h
    have hu : u = (1,2,4) := congrArg (fun x => x.2.2) h
    have hp : p = case15p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case15_strongest]
    exact case15_join
  · have hf : (p : Fin 5 → Fin 5) = case16p := congrArg Prod.fst h
    have ht : t = (0,2,3) := congrArg (fun x => x.2.1) h
    have hu : u = (1,3,4) := congrArg (fun x => x.2.2) h
    have hp : p = case16p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case16_strongest]
    exact case16_join
  · have hf : (p : Fin 5 → Fin 5) = case17p := congrArg Prod.fst h
    have ht : t = (0,2,4) := congrArg (fun x => x.2.1) h
    have hu : u = (1,3,4) := congrArg (fun x => x.2.2) h
    have hp : p = case17p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case17_strongest]
    exact case17_join
  · have hf : (p : Fin 5 → Fin 5) = case18p := congrArg Prod.fst h
    have ht : t = (0,2,4) := congrArg (fun x => x.2.1) h
    have hu : u = (1,2,3) := congrArg (fun x => x.2.2) h
    have hp : p = case18p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case18_strongest]
    exact case18_join
  · have hf : (p : Fin 5 → Fin 5) = case19p := congrArg Prod.fst h
    have ht : t = (0,3,4) := congrArg (fun x => x.2.1) h
    have hu : u = (1,2,4) := congrArg (fun x => x.2.2) h
    have hp : p = case19p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case19_strongest]
    exact case19_join
  · have hf : (p : Fin 5 → Fin 5) = case20p := congrArg Prod.fst h
    have ht : t = (0,1,3) := congrArg (fun x => x.2.1) h
    have hu : u = (0,2,4) := congrArg (fun x => x.2.2) h
    have hp : p = case20p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case20_strongest]
    exact case20_join
  · have hf : (p : Fin 5 → Fin 5) = case21p := congrArg Prod.fst h
    have ht : t = (0,1,4) := congrArg (fun x => x.2.1) h
    have hu : u = (0,2,3) := congrArg (fun x => x.2.2) h
    have hp : p = case21p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case21_strongest]
    exact case21_join
  · have hf : (p : Fin 5 → Fin 5) = case22p := congrArg Prod.fst h
    have ht : t = (0,1,3) := congrArg (fun x => x.2.1) h
    have hu : u = (0,2,4) := congrArg (fun x => x.2.2) h
    have hp : p = case22p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case22_strongest]
    exact case22_join
  · have hf : (p : Fin 5 → Fin 5) = case23p := congrArg Prod.fst h
    have ht : t = (0,1,4) := congrArg (fun x => x.2.1) h
    have hu : u = (0,2,3) := congrArg (fun x => x.2.2) h
    have hp : p = case23p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case23_strongest]
    exact case23_join
  · have hf : (p : Fin 5 → Fin 5) = case24p := congrArg Prod.fst h
    have ht : t = (0,1,2) := congrArg (fun x => x.2.1) h
    have hu : u = (0,3,4) := congrArg (fun x => x.2.2) h
    have hp : p = case24p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case24_strongest]
    exact case24_join
  · have hf : (p : Fin 5 → Fin 5) = case25p := congrArg Prod.fst h
    have ht : t = (0,1,2) := congrArg (fun x => x.2.1) h
    have hu : u = (2,3,4) := congrArg (fun x => x.2.2) h
    have hp : p = case25p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case25_strongest]
    exact case25_join
  · have hf : (p : Fin 5 → Fin 5) = case26p := congrArg Prod.fst h
    have ht : t = (0,1,4) := congrArg (fun x => x.2.1) h
    have hu : u = (2,3,4) := congrArg (fun x => x.2.2) h
    have hp : p = case26p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case26_strongest]
    exact case26_join
  · have hf : (p : Fin 5 → Fin 5) = case27p := congrArg Prod.fst h
    have ht : t = (0,1,2) := congrArg (fun x => x.2.1) h
    have hu : u = (0,3,4) := congrArg (fun x => x.2.2) h
    have hp : p = case27p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case27_strongest]
    exact case27_join
  · have hf : (p : Fin 5 → Fin 5) = case28p := congrArg Prod.fst h
    have ht : t = (0,1,3) := congrArg (fun x => x.2.1) h
    have hu : u = (0,2,4) := congrArg (fun x => x.2.2) h
    have hp : p = case28p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case28_strongest]
    exact case28_join
  · have hf : (p : Fin 5 → Fin 5) = case29p := congrArg Prod.fst h
    have ht : t = (0,1,3) := congrArg (fun x => x.2.1) h
    have hu : u = (1,2,4) := congrArg (fun x => x.2.2) h
    have hp : p = case29p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case29_strongest]
    exact case29_join
  · have hf : (p : Fin 5 → Fin 5) = case30p := congrArg Prod.fst h
    have ht : t = (0,1,4) := congrArg (fun x => x.2.1) h
    have hu : u = (0,2,3) := congrArg (fun x => x.2.2) h
    have hp : p = case30p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case30_strongest]
    exact case30_join
  · have hf : (p : Fin 5 → Fin 5) = case31p := congrArg Prod.fst h
    have ht : t = (0,1,4) := congrArg (fun x => x.2.1) h
    have hu : u = (1,2,3) := congrArg (fun x => x.2.2) h
    have hp : p = case31p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case31_strongest]
    exact case31_join
  · have hf : (p : Fin 5 → Fin 5) = case32p := congrArg Prod.fst h
    have ht : t = (0,2,3) := congrArg (fun x => x.2.1) h
    have hu : u = (1,2,4) := congrArg (fun x => x.2.2) h
    have hp : p = case32p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case32_strongest]
    exact case32_join
  · have hf : (p : Fin 5 → Fin 5) = case33p := congrArg Prod.fst h
    have ht : t = (0,2,4) := congrArg (fun x => x.2.1) h
    have hu : u = (1,2,3) := congrArg (fun x => x.2.2) h
    have hp : p = case33p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case33_strongest]
    exact case33_join
  · have hf : (p : Fin 5 → Fin 5) = case34p := congrArg Prod.fst h
    have ht : t = (0,1,3) := congrArg (fun x => x.2.1) h
    have hu : u = (0,2,4) := congrArg (fun x => x.2.2) h
    have hp : p = case34p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case34_strongest]
    exact case34_join
  · have hf : (p : Fin 5 → Fin 5) = case35p := congrArg Prod.fst h
    have ht : t = (0,1,3) := congrArg (fun x => x.2.1) h
    have hu : u = (1,2,4) := congrArg (fun x => x.2.2) h
    have hp : p = case35p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case35_strongest]
    exact case35_join
  · have hf : (p : Fin 5 → Fin 5) = case36p := congrArg Prod.fst h
    have ht : t = (0,1,4) := congrArg (fun x => x.2.1) h
    have hu : u = (0,2,3) := congrArg (fun x => x.2.2) h
    have hp : p = case36p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case36_strongest]
    exact case36_join
  · have hf : (p : Fin 5 → Fin 5) = case37p := congrArg Prod.fst h
    have ht : t = (0,1,4) := congrArg (fun x => x.2.1) h
    have hu : u = (1,2,3) := congrArg (fun x => x.2.2) h
    have hp : p = case37p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case37_strongest]
    exact case37_join
  · have hf : (p : Fin 5 → Fin 5) = case38p := congrArg Prod.fst h
    have ht : t = (0,2,3) := congrArg (fun x => x.2.1) h
    have hu : u = (1,2,4) := congrArg (fun x => x.2.2) h
    have hp : p = case38p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case38_strongest]
    exact case38_join
  · have hf : (p : Fin 5 → Fin 5) = case39p := congrArg Prod.fst h
    have ht : t = (0,2,4) := congrArg (fun x => x.2.1) h
    have hu : u = (1,2,3) := congrArg (fun x => x.2.2) h
    have hp : p = case39p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case39_strongest]
    exact case39_join
  · have hf : (p : Fin 5 → Fin 5) = case40p := congrArg Prod.fst h
    have ht : t = (0,1,2) := congrArg (fun x => x.2.1) h
    have hu : u = (0,3,4) := congrArg (fun x => x.2.2) h
    have hp : p = case40p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case40_strongest]
    exact case40_join
  · have hf : (p : Fin 5 → Fin 5) = case41p := congrArg Prod.fst h
    have ht : t = (0,1,2) := congrArg (fun x => x.2.1) h
    have hu : u = (1,3,4) := congrArg (fun x => x.2.2) h
    have hp : p = case41p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case41_strongest]
    exact case41_join
  · have hf : (p : Fin 5 → Fin 5) = case42p := congrArg Prod.fst h
    have ht : t = (0,1,2) := congrArg (fun x => x.2.1) h
    have hu : u = (2,3,4) := congrArg (fun x => x.2.2) h
    have hp : p = case42p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case42_strongest]
    exact case42_join
  · have hf : (p : Fin 5 → Fin 5) = case43p := congrArg Prod.fst h
    have ht : t = (0,1,4) := congrArg (fun x => x.2.1) h
    have hu : u = (2,3,4) := congrArg (fun x => x.2.2) h
    have hp : p = case43p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case43_strongest]
    exact case43_join
  · have hf : (p : Fin 5 → Fin 5) = case44p := congrArg Prod.fst h
    have ht : t = (0,1,2) := congrArg (fun x => x.2.1) h
    have hu : u = (0,3,4) := congrArg (fun x => x.2.2) h
    have hp : p = case44p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case44_strongest]
    exact case44_join
  · have hf : (p : Fin 5 → Fin 5) = case45p := congrArg Prod.fst h
    have ht : t = (0,1,2) := congrArg (fun x => x.2.1) h
    have hu : u = (1,3,4) := congrArg (fun x => x.2.2) h
    have hp : p = case45p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case45_strongest]
    exact case45_join
  · have hf : (p : Fin 5 → Fin 5) = case46p := congrArg Prod.fst h
    have ht : t = (0,2,4) := congrArg (fun x => x.2.1) h
    have hu : u = (1,3,4) := congrArg (fun x => x.2.2) h
    have hp : p = case46p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case46_strongest]
    exact case46_join
  · have hf : (p : Fin 5 → Fin 5) = case47p := congrArg Prod.fst h
    have ht : t = (0,3,4) := congrArg (fun x => x.2.1) h
    have hu : u = (1,2,4) := congrArg (fun x => x.2.2) h
    have hp : p = case47p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case47_strongest]
    exact case47_join
  · have hf : (p : Fin 5 → Fin 5) = case48p := congrArg Prod.fst h
    have ht : t = (0,2,4) := congrArg (fun x => x.2.1) h
    have hu : u = (1,3,4) := congrArg (fun x => x.2.2) h
    have hp : p = case48p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case48_strongest]
    exact case48_join
  · have hf : (p : Fin 5 → Fin 5) = case49p := congrArg Prod.fst h
    have ht : t = (0,3,4) := congrArg (fun x => x.2.1) h
    have hu : u = (1,2,4) := congrArg (fun x => x.2.2) h
    have hp : p = case49p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case49_strongest]
    exact case49_join
  · have hf : (p : Fin 5 → Fin 5) = case50p := congrArg Prod.fst h
    have ht : t = (0,1,4) := congrArg (fun x => x.2.1) h
    have hu : u = (2,3,4) := congrArg (fun x => x.2.2) h
    have hp : p = case50p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case50_strongest]
    exact case50_join
  · have hf : (p : Fin 5 → Fin 5) = case51p := congrArg Prod.fst h
    have ht : t = (0,1,4) := congrArg (fun x => x.2.1) h
    have hu : u = (1,2,3) := congrArg (fun x => x.2.2) h
    have hp : p = case51p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case51_strongest]
    exact case51_join
  · have hf : (p : Fin 5 → Fin 5) = case52p := congrArg Prod.fst h
    have ht : t = (0,2,4) := congrArg (fun x => x.2.1) h
    have hu : u = (1,2,3) := congrArg (fun x => x.2.2) h
    have hp : p = case52p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case52_strongest]
    exact case52_join
  · have hf : (p : Fin 5 → Fin 5) = case53p := congrArg Prod.fst h
    have ht : t = (0,3,4) := congrArg (fun x => x.2.1) h
    have hu : u = (1,2,3) := congrArg (fun x => x.2.2) h
    have hp : p = case53p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case53_strongest]
    exact case53_join
  · have hf : (p : Fin 5 → Fin 5) = case54p := congrArg Prod.fst h
    have ht : t = (0,3,4) := congrArg (fun x => x.2.1) h
    have hu : u = (1,2,4) := congrArg (fun x => x.2.2) h
    have hp : p = case54p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case54_strongest]
    exact case54_join
  · have hf : (p : Fin 5 → Fin 5) = case55p := congrArg Prod.fst h
    have ht : t = (0,1,3) := congrArg (fun x => x.2.1) h
    have hu : u = (1,2,4) := congrArg (fun x => x.2.2) h
    have hp : p = case55p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case55_strongest]
    exact case55_join
  · have hf : (p : Fin 5 → Fin 5) = case56p := congrArg Prod.fst h
    have ht : t = (0,2,3) := congrArg (fun x => x.2.1) h
    have hu : u = (1,2,4) := congrArg (fun x => x.2.2) h
    have hp : p = case56p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case56_strongest]
    exact case56_join
  · have hf : (p : Fin 5 → Fin 5) = case57p := congrArg Prod.fst h
    have ht : t = (0,1,4) := congrArg (fun x => x.2.1) h
    have hu : u = (2,3,4) := congrArg (fun x => x.2.2) h
    have hp : p = case57p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case57_strongest]
    exact case57_join
  · have hf : (p : Fin 5 → Fin 5) = case58p := congrArg Prod.fst h
    have ht : t = (0,2,4) := congrArg (fun x => x.2.1) h
    have hu : u = (1,3,4) := congrArg (fun x => x.2.2) h
    have hp : p = case58p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case58_strongest]
    exact case58_join
  · have hf : (p : Fin 5 → Fin 5) = case59p := congrArg Prod.fst h
    have ht : t = (0,1,2) := congrArg (fun x => x.2.1) h
    have hu : u = (1,3,4) := congrArg (fun x => x.2.2) h
    have hp : p = case59p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case59_strongest]
    exact case59_join
  · have hf : (p : Fin 5 → Fin 5) = case60p := congrArg Prod.fst h
    have ht : t = (0,2,4) := congrArg (fun x => x.2.1) h
    have hu : u = (1,3,4) := congrArg (fun x => x.2.2) h
    have hp : p = case60p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case60_strongest]
    exact case60_join
  · have hf : (p : Fin 5 → Fin 5) = case61p := congrArg Prod.fst h
    have ht : t = (0,3,4) := congrArg (fun x => x.2.1) h
    have hu : u = (1,2,4) := congrArg (fun x => x.2.2) h
    have hp : p = case61p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case61_strongest]
    exact case61_join
  · have hf : (p : Fin 5 → Fin 5) = case62p := congrArg Prod.fst h
    have ht : t = (0,1,4) := congrArg (fun x => x.2.1) h
    have hu : u = (2,3,4) := congrArg (fun x => x.2.2) h
    have hp : p = case62p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case62_strongest]
    exact case62_join
  · have hf : (p : Fin 5 → Fin 5) = case63p := congrArg Prod.fst h
    have ht : t = (0,2,4) := congrArg (fun x => x.2.1) h
    have hu : u = (1,3,4) := congrArg (fun x => x.2.2) h
    have hp : p = case63p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case63_strongest]
    exact case63_join
  · have hf : (p : Fin 5 → Fin 5) = case64p := congrArg Prod.fst h
    have ht : t = (0,3,4) := congrArg (fun x => x.2.1) h
    have hu : u = (1,2,4) := congrArg (fun x => x.2.2) h
    have hp : p = case64p := Equiv.ext (fun x => congrFun hf x)
    subst p
    rw [ht,hu]
    dsimp only
    rw [← case64_strongest]
    exact case64_join
end Young213
```

```lean module=YoungTermination.lean
import YoungLifting
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

namespace Young213
open Finset

def weight {n} (p : Placement n) : Nat := ∑ x : Fin n, (n - x.val) * (p x).val

 theorem split_sum {n} (f : Fin n → Nat) (i j : Fin n) (hij : i ≠ j) :
    ∑ x, f x = (∑ x ∈ (univ.erase i).erase j, f x) + f j + f i := by
  have hj : j ∈ (univ : Finset (Fin n)).erase i := by simp [Ne.symm hij]
  rw [← sum_erase_add _ _ (mem_univ i), ← sum_erase_add _ _ hj]

 theorem weight_decreases {n} {p : Placement n} {i j : Fin n}
    (hij : i < j) (hji : p j < p i) : weight (exchange p i j) < weight p := by
  have hne : i ≠ j := ne_of_lt hij
  unfold weight
  rw [split_sum _ i j hne, split_sum _ i j hne]
  have heq : (∑ x ∈ ((univ : Finset (Fin n)).erase i).erase j,
      (n-x.val) * ((exchange p i j) x).val) =
      ∑ x ∈ ((univ : Finset (Fin n)).erase i).erase j, (n-x.val) * (p x).val := by
    apply sum_congr rfl
    intro x hx
    have hxi : x ≠ i := (mem_erase.mp (mem_erase.mp hx).2).1
    have hxj : x ≠ j := (mem_erase.mp hx).1
    rw [exchange_outside p i j x hxi hxj]
  rw [heq]
  simp only [exchange_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have hw : n - j.val < n - i.val := by omega
  have hv : (p j).val < (p i).val := hji
  have hpos : 0 < (n - i.val - (n - j.val)) * ((p i).val - (p j).val) :=
    Nat.mul_pos (by omega) (by omega)
  have hw' : n-i.val = (n-j.val) + (n-i.val-(n-j.val)) := by omega
  have hv' : (p i).val = (p j).val + ((p i).val-(p j).val) := by omega
  nlinarith

 theorem step_weight {n} {b : Fin n → Nat} {p q : Placement n}
    (h : Step b p q) : weight q < weight p := by
  rcases h with ⟨_,i,j,k,hl,rfl⟩
  exact weight_decreases hl.1 hl.2.2.2.1

 theorem terminating {n} (b : Fin n → Nat) :
    WellFounded (fun q p : Placement n => Step b p q) :=
  Subrelation.wf (fun h => step_weight h) (measure weight).wf

 theorem terminal_exists {n} {b : Fin n → Nat} (hb : Monotone b)
    (p : Placement n) (hp : Valid b p) :
    ∃ t, Reach b p t ∧ Valid b t ∧ Avoid213 b t := by
  have hw := terminating b
  induction p using hw.induction with
  | h p ih =>
    by_cases ht : Terminal b p
    · exact ⟨p,.refl,hp,(terminal_iff_avoid hp).mp ht⟩
    · have he : ∃ q, Step b p q := Classical.not_not.mp ht
      obtain ⟨q,hq⟩ := he
      obtain ⟨t,hr,hv,ha⟩ := ih q hq (step_valid hb hq)
      exact ⟨t,(Relation.ReflTransGen.single hq).trans hr,hv,ha⟩

end Young213
```
