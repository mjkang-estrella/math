import ChordFourBase2
namespace Chord
set_option maxRecDepth 10000
set_option maxHeartbeats 6000000
theorem exception2_chunk0 : ∀ b4 b5 b6 b7 : Bool, boundary exception2 (side82 false false false false b4 b5 b6 b7) = 2 ∨ boundary exception2 (side82 false false false false b4 b5 b6 b7) = 4 := by decide
theorem exception2_chunk1 : ∀ b4 b5 b6 b7 : Bool, boundary exception2 (side82 true false false false b4 b5 b6 b7) = 2 ∨ boundary exception2 (side82 true false false false b4 b5 b6 b7) = 4 := by decide
theorem exception2_chunk2 : ∀ b4 b5 b6 b7 : Bool, boundary exception2 (side82 false true false false b4 b5 b6 b7) = 2 ∨ boundary exception2 (side82 false true false false b4 b5 b6 b7) = 4 := by decide
theorem exception2_chunk3 : ∀ b4 b5 b6 b7 : Bool, boundary exception2 (side82 true true false false b4 b5 b6 b7) = 2 ∨ boundary exception2 (side82 true true false false b4 b5 b6 b7) = 4 := by decide
end Chord
