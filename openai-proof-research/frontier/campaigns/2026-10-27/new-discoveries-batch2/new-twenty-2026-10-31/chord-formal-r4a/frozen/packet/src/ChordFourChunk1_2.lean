import ChordFourBase1
namespace Chord
set_option maxRecDepth 10000
set_option maxHeartbeats 6000000
theorem exception1_chunk8 : ∀ b4 b5 b6 b7 : Bool, boundary exception1 (side81 false false false true b4 b5 b6 b7) = 2 ∨ boundary exception1 (side81 false false false true b4 b5 b6 b7) = 4 := by decide
theorem exception1_chunk9 : ∀ b4 b5 b6 b7 : Bool, boundary exception1 (side81 true false false true b4 b5 b6 b7) = 2 ∨ boundary exception1 (side81 true false false true b4 b5 b6 b7) = 4 := by decide
theorem exception1_chunk10 : ∀ b4 b5 b6 b7 : Bool, boundary exception1 (side81 false true false true b4 b5 b6 b7) = 2 ∨ boundary exception1 (side81 false true false true b4 b5 b6 b7) = 4 := by decide
theorem exception1_chunk11 : ∀ b4 b5 b6 b7 : Bool, boundary exception1 (side81 true true false true b4 b5 b6 b7) = 2 ∨ boundary exception1 (side81 true true false true b4 b5 b6 b7) = 4 := by decide
end Chord
