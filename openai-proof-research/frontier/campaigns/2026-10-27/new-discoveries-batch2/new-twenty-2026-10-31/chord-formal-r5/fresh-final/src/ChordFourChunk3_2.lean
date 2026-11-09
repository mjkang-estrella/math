import ChordFourBase3
namespace Chord
set_option maxRecDepth 10000
set_option maxHeartbeats 6000000
theorem exception3_chunk8 : ∀ b4 b5 b6 b7 : Bool, boundary exception3 (side83 false false false true b4 b5 b6 b7) = 2 ∨ boundary exception3 (side83 false false false true b4 b5 b6 b7) = 4 := by decide
theorem exception3_chunk9 : ∀ b4 b5 b6 b7 : Bool, boundary exception3 (side83 true false false true b4 b5 b6 b7) = 2 ∨ boundary exception3 (side83 true false false true b4 b5 b6 b7) = 4 := by decide
theorem exception3_chunk10 : ∀ b4 b5 b6 b7 : Bool, boundary exception3 (side83 false true false true b4 b5 b6 b7) = 2 ∨ boundary exception3 (side83 false true false true b4 b5 b6 b7) = 4 := by decide
theorem exception3_chunk11 : ∀ b4 b5 b6 b7 : Bool, boundary exception3 (side83 true true false true b4 b5 b6 b7) = 2 ∨ boundary exception3 (side83 true true false true b4 b5 b6 b7) = 4 := by decide
end Chord
