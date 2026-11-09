import ChordModel3Surgery
namespace Chord.Model3

/-- CONDITIONAL: Deletion remains open in round 3A. -/
theorem conj34_intended_model3
    (del : Deletion) (existence : RepresentativeExistence)
    (five : FiveChordLemma) (triangle : TriangleReduction) (rigidity : TriangleRigidity)
    (n : Nat) (hn : 3 ≤ n) (h4 : n ≠ 4) :
    Range12 (r3Block n hn) ∧
    ∀ D : Diagram n, Range12 D → Equivalent D (r3Block n hn) :=
  Model2.conj34_intended_model2 del existence five triangle rigidity n hn h4

theorem conj34_n4_model3 (enumeration : FourChordEnumeration) : ExactlyClasses 4 4 :=
  Model2.conj34_n4_model2 enumeration

theorem conj34_literal_false_model3 :
    (∀ D : Diagram 1, ¬Range12 D) ∧ (∀ D : Diagram 2, ¬Range12 D) :=
  Model2.conj34_literal_false_model2

#print axioms cycles_eq_orbitCount
#print axioms boundary_eq_orbitCount
#print axioms orbitCount_of_section
#print axioms deletion_zero
#print axioms deletion_one
#print axioms deletion_of_surgery
#print axioms conj34_intended_model3
end Chord.Model3
