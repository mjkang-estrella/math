import ChordFourBase3
namespace Chord
set_option maxRecDepth 10000
set_option maxHeartbeats 6000000
theorem exception3_chunk0 : ∀ b4 b5 b6 b7 : Bool, boundary exception3 (side83 false false false false b4 b5 b6 b7) = 2 ∨ boundary exception3 (side83 false false false false b4 b5 b6 b7) = 4 := by decide
theorem exception3_chunk1 : ∀ b4 b5 b6 b7 : Bool, boundary exception3 (side83 true false false false b4 b5 b6 b7) = 2 ∨ boundary exception3 (side83 true false false false b4 b5 b6 b7) = 4 := by decide
theorem exception3_chunk2 : ∀ b4 b5 b6 b7 : Bool, boundary exception3 (side83 false true false false b4 b5 b6 b7) = 2 ∨ boundary exception3 (side83 false true false false b4 b5 b6 b7) = 4 := by decide
theorem exception3_chunk3 : ∀ b4 b5 b6 b7 : Bool, boundary exception3 (side83 true true false false b4 b5 b6 b7) = 2 ∨ boundary exception3 (side83 true true false false b4 b5 b6 b7) = 4 := by decide
end Chord
