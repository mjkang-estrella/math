import ChordFourBase0
namespace Chord
set_option maxRecDepth 10000
set_option maxHeartbeats 6000000
theorem exception0_chunk8 : ∀ b4 b5 b6 b7 : Bool, boundary exception0 (side80 false false false true b4 b5 b6 b7) = 2 ∨ boundary exception0 (side80 false false false true b4 b5 b6 b7) = 4 := by decide
theorem exception0_chunk9 : ∀ b4 b5 b6 b7 : Bool, boundary exception0 (side80 true false false true b4 b5 b6 b7) = 2 ∨ boundary exception0 (side80 true false false true b4 b5 b6 b7) = 4 := by decide
theorem exception0_chunk10 : ∀ b4 b5 b6 b7 : Bool, boundary exception0 (side80 false true false true b4 b5 b6 b7) = 2 ∨ boundary exception0 (side80 false true false true b4 b5 b6 b7) = 4 := by decide
theorem exception0_chunk11 : ∀ b4 b5 b6 b7 : Bool, boundary exception0 (side80 true true false true b4 b5 b6 b7) = 2 ∨ boundary exception0 (side80 true true false true b4 b5 b6 b7) = 4 := by decide
end Chord
