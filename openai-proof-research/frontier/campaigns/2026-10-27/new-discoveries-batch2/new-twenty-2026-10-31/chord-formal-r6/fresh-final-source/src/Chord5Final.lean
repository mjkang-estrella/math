import Chord5OrbitFive
import Chord5EndFace
import Chord5ErasureSetup
import Chord5Graph
import ChordModel4Final
namespace Chord.Round5
/-- Round 5 partial endpoint: exactly the four remaining mathematical Props. -/
theorem conj34_intended
    (erase : Model3.BandErasure) (surgery : Comb4.EndEdgeSurgery)
    (split : Comb4.MonochromaticSplit) (rigidity : Comb4.TriangleRigiditySix)
    (n : Nat) (hn : 3 ≤ n) (h4 : n ≠ 4) :
    Range12 (r3Block n hn) ∧
    ∀ D : Diagram n, Range12 D → Equivalent D (r3Block n hn) :=
  Comb4.conj34_intended (Comb4.step_of_surgery surgery)
    (Model4.heredity_of_bandErasure erase) (triangleReduction_of_split split) rigidity n hn h4

theorem conj34_n4 : ExactlyClasses 4 4 := Comb4.conj34_n4

theorem conj34_literal_false :
    (∀ D : Diagram 1, ¬Range12 D) ∧ (∀ D : Diagram 2, ¬Range12 D) :=
  Comb4.conj34_literal_false

#print axioms conj34_intended
#print axioms conj34_n4
#print axioms conj34_literal_false
end Chord.Round5
