import ChordFourBase1
namespace Chord
set_option maxRecDepth 10000
set_option maxHeartbeats 6000000
theorem exception1_chunk12 : ∀ b4 b5 b6 b7 : Bool, boundary exception1 (side81 false false true true b4 b5 b6 b7) = 2 ∨ boundary exception1 (side81 false false true true b4 b5 b6 b7) = 4 := by decide
theorem exception1_chunk13 : ∀ b4 b5 b6 b7 : Bool, boundary exception1 (side81 true false true true b4 b5 b6 b7) = 2 ∨ boundary exception1 (side81 true false true true b4 b5 b6 b7) = 4 := by decide
theorem exception1_chunk14 : ∀ b4 b5 b6 b7 : Bool, boundary exception1 (side81 false true true true b4 b5 b6 b7) = 2 ∨ boundary exception1 (side81 false true true true b4 b5 b6 b7) = 4 := by decide
theorem exception1_chunk15 : ∀ b4 b5 b6 b7 : Bool, boundary exception1 (side81 true true true true b4 b5 b6 b7) = 2 ∨ boundary exception1 (side81 true true true true b4 b5 b6 b7) = 4 := by decide
end Chord
