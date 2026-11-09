import Chord6Split
import Chord5Final
namespace Chord.Round6

/-- The planarity and odd-cycle reductions now need only band erasure. -/
theorem planarity_of_bandErasure (erase : Model3.BandErasure) : BipartitePlanarity :=
  Comb4.planarity_of_split (monochromaticSplit_of_bandErasure erase)

theorem triangleReduction_of_bandErasure (erase : Model3.BandErasure) : TriangleReduction :=
  Round5.triangleReduction_of_split (monochromaticSplit_of_bandErasure erase)

/-- Partial round-6 endpoint. Three independent mathematical hypotheses remain.
MonochromaticSplit is derived internally from BandErasure. -/
theorem conj34_intended
    (erase : Model3.BandErasure) (surgery : Comb4.EndEdgeSurgery)
    (rigidity : Comb4.TriangleRigiditySix)
    (n : Nat) (hn : 3 ≤ n) (h4 : n ≠ 4) :
    Range12 (r3Block n hn) ∧
    ∀ D : Diagram n, Range12 D → Equivalent D (r3Block n hn) :=
  Round5.conj34_intended erase surgery
    (monochromaticSplit_of_bandErasure erase) rigidity n hn h4

theorem conj34_n4 : ExactlyClasses 4 4 := Round5.conj34_n4

theorem conj34_literal_false :
    (∀ D : Diagram 1, ¬Range12 D) ∧ (∀ D : Diagram 2, ¬Range12 D) :=
  Round5.conj34_literal_false

#print axioms conj34_intended
#print axioms conj34_n4
#print axioms conj34_literal_false
end Chord.Round6
