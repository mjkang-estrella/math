import Chord7EndBand
import Chord7Compression
namespace Chord.Round7

/-- Round 7 remains conditional on these three unchanged obligations. -/
theorem conj34_intended
    (erase : Model3.BandErasure) (surgery : Comb4.EndEdgeSurgery)
    (rigidity : Comb4.TriangleRigiditySix)
    (n : Nat) (hn : 3 ≤ n) (h4 : n ≠ 4) :
    Range12 (r3Block n hn) ∧
    ∀ D : Diagram n, Range12 D → Equivalent D (r3Block n hn) :=
  Round6.conj34_intended erase surgery rigidity n hn h4

theorem conj34_n4 : ExactlyClasses 4 4 := Round6.conj34_n4

theorem conj34_literal_false :
    (∀ D : Diagram 1, ¬Range12 D) ∧ (∀ D : Diagram 2, ¬Range12 D) :=
  Round6.conj34_literal_false

#print axioms conj34_intended
#print axioms conj34_n4
#print axioms conj34_literal_false
end Chord.Round7
