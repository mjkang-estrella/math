import pathlib,json
L=pathlib.Path(__file__).resolve().parents[1]
w=json.loads((L/'outputs/grid-3-5-witness.json').read_text())['word']
txt='''import Definitions
namespace Toroidal
def witness : List (Vertex 3 5) := [
'''+',\n'.join(f' (⟨{x//5}, by decide⟩, ⟨{x%5}, by decide⟩)' for x in w)+''']
theorem witness_represents : Represents 3 5 3 witness := by decide
theorem representation_exists : HasRepresentation 3 5 3 := ⟨witness, witness_represents⟩
theorem number_le_three : representationNumber 3 5 ≤ (3 : WithTop Nat) := by
 classical
 have h : ∃ k, 0 < k ∧ HasRepresentation 3 5 k :=
   ⟨3, by decide, representation_exists⟩
 unfold representationNumber
 rw [dif_pos h]
 exact_mod_cast Nat.find_min' h (show 0 < 3 ∧ HasRepresentation 3 5 3 from ⟨by decide, representation_exists⟩)
theorem mathdb_369421 : ¬ Conjecture1 := by
 intro h
 have hh := h 3 5 (by decide) (by decide) (by decide)
 have h43 : (4 : WithTop Nat) ≤ 3 := le_trans hh number_le_three
 exact (by decide : ¬ (4 : WithTop Nat) ≤ 3) h43
#print axioms witness_represents
#print axioms number_le_three
#print axioms mathdb_369421
end Toroidal
'''
(L/'lean/Witness.lean').write_text(txt)
