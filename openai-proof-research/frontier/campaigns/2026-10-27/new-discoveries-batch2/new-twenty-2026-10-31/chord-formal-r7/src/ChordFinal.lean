import ChordRemaining
import ChordBridgeChecks
import ChordControls
import ChordFourWitnesses
namespace Chord

/-- CONDITIONAL endpoint. These five explicit Prop hypotheses remain unproved. -/
theorem conj34_intended
    (existence : RepresentativeExistence) (heredity : Heredity)
    (five : FiveChordLemma) (triangle : TriangleReduction) (rigidity : TriangleRigidity)
    (n : Nat) (hn : 3 ≤ n) (h4 : n ≠ 4) :
    Range12 (r3Block n hn) ∧
    ∀ D : Diagram n, Range12 D → Equivalent D (r3Block n hn) := by
  refine ⟨existence n hn, ?_⟩
  intro D hD
  have maxD : MaxTwo D := by
    intro g hg
    have := (hD g).mp hg
    omega
  have nonzero : ¬genusRange D 0 := by
    intro h
    have := (hD 0).mp h
    omega
  have localFive : ∀ A : Diagram 5, Subdiagram A D → FiveProperty A := by
    intro A hA
    exact five A (heredity 5 n A D hA maxD)
  exact rigidity n hn h4 D (triangle n hn D nonzero localFive) localFive

/-- CONDITIONAL finite endpoint, explicitly awaiting enumeration and completeness. -/
theorem conj34_n4 (enumeration : FourChordEnumeration) : ExactlyClasses 4 4 := enumeration

/-- Unconditional literal defect, including both exceptional small sizes. -/
theorem conj34_literal_false :
    (∀ D : Diagram 1, ¬Range12 D) ∧ (∀ D : Diagram 2, ¬Range12 D) :=
  ⟨literal_false_n1, literal_false_n2⟩

theorem printed_conjecture_false :
    ¬ (∀ n, 1 ≤ n → n ≠ 4 → ∃ D : Diagram n, Range12 D) := by
  intro h
  obtain ⟨D,hD⟩ := h 1 (by decide) (by decide)
  exact literal_false_n1 D hD

#print axioms conj34_intended
#print axioms conj34_n4
#print axioms conj34_literal_false
#print axioms printed_conjecture_false
#print axioms genusRange_r3
end Chord
