import ChordFourBase0
namespace Chord
set_option maxRecDepth 10000
set_option maxHeartbeats 6000000
theorem exception0_chunk0 : ∀ b4 b5 b6 b7 : Bool, boundary exception0 (side80 false false false false b4 b5 b6 b7) = 2 ∨ boundary exception0 (side80 false false false false b4 b5 b6 b7) = 4 := by decide
theorem exception0_chunk1 : ∀ b4 b5 b6 b7 : Bool, boundary exception0 (side80 true false false false b4 b5 b6 b7) = 2 ∨ boundary exception0 (side80 true false false false b4 b5 b6 b7) = 4 := by decide
theorem exception0_chunk2 : ∀ b4 b5 b6 b7 : Bool, boundary exception0 (side80 false true false false b4 b5 b6 b7) = 2 ∨ boundary exception0 (side80 false true false false b4 b5 b6 b7) = 4 := by decide
theorem exception0_chunk3 : ∀ b4 b5 b6 b7 : Bool, boundary exception0 (side80 true true false false b4 b5 b6 b7) = 2 ∨ boundary exception0 (side80 true true false false b4 b5 b6 b7) = 4 := by decide
end Chord
