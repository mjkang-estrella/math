import ChordFourBase1
namespace Chord
set_option maxRecDepth 10000
set_option maxHeartbeats 6000000
theorem exception1_chunk4 : ∀ b4 b5 b6 b7 : Bool, boundary exception1 (side81 false false true false b4 b5 b6 b7) = 2 ∨ boundary exception1 (side81 false false true false b4 b5 b6 b7) = 4 := by decide
theorem exception1_chunk5 : ∀ b4 b5 b6 b7 : Bool, boundary exception1 (side81 true false true false b4 b5 b6 b7) = 2 ∨ boundary exception1 (side81 true false true false b4 b5 b6 b7) = 4 := by decide
theorem exception1_chunk6 : ∀ b4 b5 b6 b7 : Bool, boundary exception1 (side81 false true true false b4 b5 b6 b7) = 2 ∨ boundary exception1 (side81 false true true false b4 b5 b6 b7) = 4 := by decide
theorem exception1_chunk7 : ∀ b4 b5 b6 b7 : Bool, boundary exception1 (side81 true true true false b4 b5 b6 b7) = 2 ∨ boundary exception1 (side81 true true true false b4 b5 b6 b7) = 4 := by decide
end Chord
