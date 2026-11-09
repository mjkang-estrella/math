import ChordModel2OrbitCorrect
import ChordModel2Face
import ChordModel2Heredity
import ChordFinal
namespace Chord.Model2

/-- Exact independent model obligations still open in this lane. -/
def Remaining2A : Prop := DartBridge ∧ Deletion

/-- Both generic permutation certification targets are unconditional. -/
theorem permutation_certification : OrbitCounterCorrect ∧ FacePermutationCorrect :=
  ⟨orbitCounterCorrect, facePermutationCorrect⟩

/-- Euler realization and heredity are now consequences of the single deletion law. -/
theorem deletion_consequences (del : Deletion) : EulerRealization ∧ Heredity :=
  ⟨euler_of_deletion del, heredity_of_deletion del⟩

/-- CONDITIONAL. The five remaining inputs are not proved by this lane. -/
theorem conj34_intended_model2
    (del : Deletion) (existence : RepresentativeExistence)
    (five : FiveChordLemma) (triangle : TriangleReduction) (rigidity : TriangleRigidity)
    (n : Nat) (hn : 3 ≤ n) (h4 : n ≠ 4) :
    Range12 (r3Block n hn) ∧
    ∀ D : Diagram n, Range12 D → Equivalent D (r3Block n hn) :=
  Chord.conj34_intended existence (heredity_of_deletion del) five triangle rigidity n hn h4

theorem conj34_n4_model2 (enumeration : FourChordEnumeration) : ExactlyClasses 4 4 :=
  Chord.conj34_n4 enumeration

theorem conj34_literal_false_model2 :
    (∀ D : Diagram 1, ¬Range12 D) ∧ (∀ D : Diagram 2, ¬Range12 D) :=
  Chord.conj34_literal_false

#print axioms orbitCounterCorrect
#print axioms facePermutationCorrect
#print axioms euler_of_deletion
#print axioms heredity_of_deletion
#print axioms conj34_intended_model2
#print axioms conj34_n4_model2
#print axioms conj34_literal_false_model2
end Chord.Model2
