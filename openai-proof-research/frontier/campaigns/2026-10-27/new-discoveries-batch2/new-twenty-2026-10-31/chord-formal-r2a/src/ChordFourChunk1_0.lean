import ChordFourBase1
namespace Chord
set_option maxRecDepth 10000
set_option maxHeartbeats 6000000
theorem exception1_chunk0 : ∀ b4 b5 b6 b7 : Bool, boundary exception1 (side81 false false false false b4 b5 b6 b7) = 2 ∨ boundary exception1 (side81 false false false false b4 b5 b6 b7) = 4 := by decide
theorem exception1_chunk1 : ∀ b4 b5 b6 b7 : Bool, boundary exception1 (side81 true false false false b4 b5 b6 b7) = 2 ∨ boundary exception1 (side81 true false false false b4 b5 b6 b7) = 4 := by decide
theorem exception1_chunk2 : ∀ b4 b5 b6 b7 : Bool, boundary exception1 (side81 false true false false b4 b5 b6 b7) = 2 ∨ boundary exception1 (side81 false true false false b4 b5 b6 b7) = 4 := by decide
theorem exception1_chunk3 : ∀ b4 b5 b6 b7 : Bool, boundary exception1 (side81 true true false false b4 b5 b6 b7) = 2 ∨ boundary exception1 (side81 true true false false b4 b5 b6 b7) = 4 := by decide
end Chord
