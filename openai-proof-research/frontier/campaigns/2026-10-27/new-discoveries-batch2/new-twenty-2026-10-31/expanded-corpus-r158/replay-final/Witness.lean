import Definitions
namespace Toroidal
def witness : List (Vertex 3 5) := [
 (⟨0, by decide⟩, ⟨0, by decide⟩),
 (⟨1, by decide⟩, ⟨3, by decide⟩),
 (⟨0, by decide⟩, ⟨4, by decide⟩),
 (⟨1, by decide⟩, ⟨0, by decide⟩),
 (⟨1, by decide⟩, ⟨4, by decide⟩),
 (⟨2, by decide⟩, ⟨1, by decide⟩),
 (⟨2, by decide⟩, ⟨2, by decide⟩),
 (⟨2, by decide⟩, ⟨3, by decide⟩),
 (⟨2, by decide⟩, ⟨0, by decide⟩),
 (⟨0, by decide⟩, ⟨1, by decide⟩),
 (⟨0, by decide⟩, ⟨2, by decide⟩),
 (⟨1, by decide⟩, ⟨1, by decide⟩),
 (⟨2, by decide⟩, ⟨1, by decide⟩),
 (⟨0, by decide⟩, ⟨0, by decide⟩),
 (⟨0, by decide⟩, ⟨1, by decide⟩),
 (⟨2, by decide⟩, ⟨4, by decide⟩),
 (⟨1, by decide⟩, ⟨0, by decide⟩),
 (⟨2, by decide⟩, ⟨0, by decide⟩),
 (⟨0, by decide⟩, ⟨3, by decide⟩),
 (⟨0, by decide⟩, ⟨4, by decide⟩),
 (⟨1, by decide⟩, ⟨2, by decide⟩),
 (⟨0, by decide⟩, ⟨0, by decide⟩),
 (⟨1, by decide⟩, ⟨3, by decide⟩),
 (⟨1, by decide⟩, ⟨4, by decide⟩),
 (⟨1, by decide⟩, ⟨1, by decide⟩),
 (⟨1, by decide⟩, ⟨0, by decide⟩),
 (⟨2, by decide⟩, ⟨2, by decide⟩),
 (⟨2, by decide⟩, ⟨1, by decide⟩),
 (⟨0, by decide⟩, ⟨2, by decide⟩),
 (⟨0, by decide⟩, ⟨1, by decide⟩),
 (⟨1, by decide⟩, ⟨2, by decide⟩),
 (⟨1, by decide⟩, ⟨1, by decide⟩),
 (⟨2, by decide⟩, ⟨3, by decide⟩),
 (⟨2, by decide⟩, ⟨2, by decide⟩),
 (⟨0, by decide⟩, ⟨3, by decide⟩),
 (⟨0, by decide⟩, ⟨2, by decide⟩),
 (⟨1, by decide⟩, ⟨3, by decide⟩),
 (⟨2, by decide⟩, ⟨4, by decide⟩),
 (⟨2, by decide⟩, ⟨0, by decide⟩),
 (⟨2, by decide⟩, ⟨3, by decide⟩),
 (⟨0, by decide⟩, ⟨4, by decide⟩),
 (⟨0, by decide⟩, ⟨3, by decide⟩),
 (⟨1, by decide⟩, ⟨2, by decide⟩),
 (⟨1, by decide⟩, ⟨4, by decide⟩),
 (⟨2, by decide⟩, ⟨4, by decide⟩)]
theorem witness_represents : Represents 3 5 3 witness := by
 unfold Represents Alternates
 decide
theorem representation_exists : HasRepresentation 3 5 3 := ⟨witness, witness_represents⟩
theorem number_le_three : representationNumber 3 5 ≤ (3 : WithTop Nat) := by
 classical
 have h : ∃ k, 0 < k ∧ HasRepresentation 3 5 k :=
   ⟨3, by decide, representation_exists⟩
 unfold representationNumber
 rw [dite_eq_left h]
 exact WithTop.coe_le_coe.mpr (Nat.find_min' h (show 0 < 3 ∧ HasRepresentation 3 5 3 from ⟨by decide, representation_exists⟩))
theorem mathdb_369421 : ¬ Conjecture1 := by
 intro h
 have hh := h 3 5 (by decide) (by decide) (by decide)
 have h43 : (4 : WithTop Nat) ≤ 3 := le_trans hh number_le_three
 exact (by decide : ¬ (4 : WithTop Nat) ≤ 3) h43
#print axioms witness_represents
#print axioms number_le_three
#print axioms mathdb_369421
end Toroidal
