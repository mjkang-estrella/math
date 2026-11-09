import ChordFourBase2
namespace Chord
set_option maxRecDepth 10000
set_option maxHeartbeats 6000000
theorem exception2_chunk8 : ∀ b4 b5 b6 b7 : Bool, boundary exception2 (side82 false false false true b4 b5 b6 b7) = 2 ∨ boundary exception2 (side82 false false false true b4 b5 b6 b7) = 4 := by decide
theorem exception2_chunk9 : ∀ b4 b5 b6 b7 : Bool, boundary exception2 (side82 true false false true b4 b5 b6 b7) = 2 ∨ boundary exception2 (side82 true false false true b4 b5 b6 b7) = 4 := by decide
theorem exception2_chunk10 : ∀ b4 b5 b6 b7 : Bool, boundary exception2 (side82 false true false true b4 b5 b6 b7) = 2 ∨ boundary exception2 (side82 false true false true b4 b5 b6 b7) = 4 := by decide
theorem exception2_chunk11 : ∀ b4 b5 b6 b7 : Bool, boundary exception2 (side82 true true false true b4 b5 b6 b7) = 2 ∨ boundary exception2 (side82 true true false true b4 b5 b6 b7) = 4 := by decide
end Chord
