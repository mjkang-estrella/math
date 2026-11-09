import ChordComb2Four0
import ChordComb2Four1
import ChordComb2Four2
import ChordComb2Four3
import ChordComb2Four4
import ChordComb2Four5
import ChordComb2Four6
namespace Chord.Comb2
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
theorem four_complete (D : Diagram 4) : Range12 D → ∃ i, Equivalent D (fourReps i) := by
  have opts : D.partner 0 = 1 ∨ D.partner 0 = 2 ∨ D.partner 0 = 3 ∨ D.partner 0 = 4 ∨ D.partner 0 = 5 ∨ D.partner 0 = 6 ∨ D.partner 0 = 7 := by
    have inv := D.involutive 0
    have nf := D.noFixed 0
    generalize hv : D.partner 0 = v
    fin_cases v <;> simp_all
  rcases opts with h1 | h2 | h3 | h4 | h5 | h6 | h7
  · exact closed4_0 D h1 (by simpa only [h1] using D.involutive 0)
  · exact closed4_1 D h2 (by simpa only [h2] using D.involutive 0)
  · exact closed4_2 D h3 (by simpa only [h3] using D.involutive 0)
  · exact closed4_3 D h4 (by simpa only [h4] using D.involutive 0)
  · exact closed4_4 D h5 (by simpa only [h5] using D.involutive 0)
  · exact closed4_5 D h6 (by simpa only [h6] using D.involutive 0)
  · exact closed4_6 D h7 (by simpa only [h7] using D.involutive 0)
theorem fourChordEnumeration : FourChordEnumeration := ⟨fourReps, fourReps_range, fourReps_distinct, four_complete⟩
#print axioms fourChordEnumeration
end Chord.Comb2
