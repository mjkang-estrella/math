import ChordFourBase2
namespace Chord
set_option maxRecDepth 10000
set_option maxHeartbeats 6000000
theorem exception2_chunk12 : ∀ b4 b5 b6 b7 : Bool, boundary exception2 (side82 false false true true b4 b5 b6 b7) = 2 ∨ boundary exception2 (side82 false false true true b4 b5 b6 b7) = 4 := by decide
theorem exception2_chunk13 : ∀ b4 b5 b6 b7 : Bool, boundary exception2 (side82 true false true true b4 b5 b6 b7) = 2 ∨ boundary exception2 (side82 true false true true b4 b5 b6 b7) = 4 := by decide
theorem exception2_chunk14 : ∀ b4 b5 b6 b7 : Bool, boundary exception2 (side82 false true true true b4 b5 b6 b7) = 2 ∨ boundary exception2 (side82 false true true true b4 b5 b6 b7) = 4 := by decide
theorem exception2_chunk15 : ∀ b4 b5 b6 b7 : Bool, boundary exception2 (side82 true true true true b4 b5 b6 b7) = 2 ∨ boundary exception2 (side82 true true true true b4 b5 b6 b7) = 4 := by decide
end Chord
