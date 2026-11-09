import ChordFourBase0
namespace Chord
set_option maxRecDepth 10000
set_option maxHeartbeats 6000000
theorem exception0_chunk12 : ∀ b4 b5 b6 b7 : Bool, boundary exception0 (side80 false false true true b4 b5 b6 b7) = 2 ∨ boundary exception0 (side80 false false true true b4 b5 b6 b7) = 4 := by decide
theorem exception0_chunk13 : ∀ b4 b5 b6 b7 : Bool, boundary exception0 (side80 true false true true b4 b5 b6 b7) = 2 ∨ boundary exception0 (side80 true false true true b4 b5 b6 b7) = 4 := by decide
theorem exception0_chunk14 : ∀ b4 b5 b6 b7 : Bool, boundary exception0 (side80 false true true true b4 b5 b6 b7) = 2 ∨ boundary exception0 (side80 false true true true b4 b5 b6 b7) = 4 := by decide
theorem exception0_chunk15 : ∀ b4 b5 b6 b7 : Bool, boundary exception0 (side80 true true true true b4 b5 b6 b7) = 2 ∨ boundary exception0 (side80 true true true true b4 b5 b6 b7) = 4 := by decide
end Chord
