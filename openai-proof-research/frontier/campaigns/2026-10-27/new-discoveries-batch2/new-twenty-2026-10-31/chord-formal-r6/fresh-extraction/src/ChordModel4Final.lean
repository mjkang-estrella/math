import ChordModel4Normalization
namespace Chord.Model4
open Model3

/-- PARTIAL round 4A: band erasure and the combinatorial hypotheses remain open. -/
theorem conj34_intended_model4
    (erase : BandErasure) (existence : RepresentativeExistence)
    (five : FiveChordLemma) (triangle : TriangleReduction) (rigidity : TriangleRigidity)
    (n : Nat) (hn : 3 ≤ n) (h4 : n ≠ 4) :
    Range12 (r3Block n hn) ∧
    ∀ D : Diagram n, Range12 D → Equivalent D (r3Block n hn) :=
  Model2.conj34_intended_model2 (deletion_of_bandErasure erase)
    existence five triangle rigidity n hn h4

theorem conj34_n4_model4 (enumeration : FourChordEnumeration) : ExactlyClasses 4 4 :=
  Model2.conj34_n4_model2 enumeration

theorem conj34_literal_false_model4 :
    (∀ D : Diagram 1, ¬Range12 D) ∧ (∀ D : Diagram 2, ¬Range12 D) :=
  Model2.conj34_literal_false_model2

#print axioms swapCycleLaw_proved
#print axioms orbitCount_removeNone
#print axioms orbitCount_optionCongr
#print axioms orbitCount_of_retraction
#print axioms bandErasure_zero
#print axioms bandErasure_one
#print axioms deletion_of_bandErasure
#print axioms euler_of_bandErasure
#print axioms heredity_of_bandErasure
#print axioms conj34_intended_model4
#print axioms conj34_n4_model4
#print axioms conj34_literal_false_model4
end Chord.Model4
