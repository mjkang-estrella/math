import ChordComb2Five
import ChordComb2Four
import ChordComb2Three
namespace Chord.Comb2

/-- The unresolved arc argument now only concerns n ≥ 5. -/
def TriangleRigidityLarge : Prop := ∀ n (hn : 5 ≤ n), ∀ D : Diagram n,
  HasTriangle D →
  (∀ A : Diagram 5, Subdiagram A D → FiveProperty A) →
  Equivalent D (r3Block n (by omega))

theorem triangleRigidity_of_large (h : TriangleRigidityLarge) : TriangleRigidity := by
  intro n hn h4 D ht hf
  by_cases h3 : n=3
  · subst n
    exact triangleRigidity_three D ht
  · exact h n (by omega) D ht hf

/-- Unresolved induction step; the base is the frozen kernel theorem. -/
def RepresentativeStep : Prop := ∀ n (hn : 3 ≤ n),
  Range12 (r3Block n hn) → Range12 (r3Block (n+1) (by omega))

theorem representativeExistence_of_step (step : RepresentativeStep) : RepresentativeExistence := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact genusRange_r3
  | succ n hn ih => exact step n hn ih

/-- CONDITIONAL. FiveChordLemma is discharged; three original combinatorial
Props and Heredity remain in this direct endpoint. -/
theorem conj34_intended
    (existence : RepresentativeExistence) (heredity : Heredity)
    (triangle : TriangleReduction) (rigidity : TriangleRigidity)
    (n : Nat) (hn : 3 ≤ n) (h4 : n ≠ 4) :
    Range12 (r3Block n hn) ∧
    ∀ D : Diagram n, Range12 D → Equivalent D (r3Block n hn) :=
  Chord.conj34_intended existence heredity fiveChordLemma triangle rigidity n hn h4

/-- Alternative conditional endpoint exposing the induction step and n ≥ 5 arc target. -/
theorem conj34_intended_reduced
    (step : RepresentativeStep) (heredity : Heredity)
    (triangle : TriangleReduction) (rigidity : TriangleRigidityLarge)
    (n : Nat) (hn : 3 ≤ n) (h4 : n ≠ 4) :
    Range12 (r3Block n hn) ∧
    ∀ D : Diagram n, Range12 D → Equivalent D (r3Block n hn) :=
  conj34_intended (representativeExistence_of_step step) heredity triangle
    (triangleRigidity_of_large rigidity) n hn h4

/-- Unconditional exactly-four classification, using the literal equivalence closure. -/
theorem conj34_n4 : ExactlyClasses 4 4 := fourChordEnumeration

theorem conj34_literal_false :
    (∀ D : Diagram 1, ¬Range12 D) ∧ (∀ D : Diagram 2, ¬Range12 D) :=
  Chord.conj34_literal_false

#print axioms fiveChordLemma
#print axioms fourChordEnumeration
#print axioms triangleRigidity_three
#print axioms representativeExistence_of_step
#print axioms conj34_intended
#print axioms conj34_n4
end Chord.Comb2
namespace Chord.Comb2
/-- A formal negative control against accidentally claiming uniqueness at n = 4. -/
theorem negative_unique_four :
    ¬ (∃ D : Diagram 4, ∀ E : Diagram 4, Range12 E → Equivalent E D) := by
  rintro ⟨D,h⟩
  have h0 := h (fourReps 0) (fourReps_range 0)
  have h1 := h (fourReps 1) (fourReps_range 1)
  have he : Equivalent (fourReps 0) (fourReps 1) :=
    Relation.EqvGen.trans _ _ _ h0 (Relation.EqvGen.symm _ _ h1)
  have hf := fourReps_distinct 0 1 he
  exact (by decide : (0 : Fin 4) ≠ 1) hf
end Chord.Comb2
