import ChordFourBase3
namespace Chord
set_option maxRecDepth 10000
set_option maxHeartbeats 6000000
theorem exception3_chunk12 : ∀ b4 b5 b6 b7 : Bool, boundary exception3 (side83 false false true true b4 b5 b6 b7) = 2 ∨ boundary exception3 (side83 false false true true b4 b5 b6 b7) = 4 := by decide
theorem exception3_chunk13 : ∀ b4 b5 b6 b7 : Bool, boundary exception3 (side83 true false true true b4 b5 b6 b7) = 2 ∨ boundary exception3 (side83 true false true true b4 b5 b6 b7) = 4 := by decide
theorem exception3_chunk14 : ∀ b4 b5 b6 b7 : Bool, boundary exception3 (side83 false true true true b4 b5 b6 b7) = 2 ∨ boundary exception3 (side83 false true true true b4 b5 b6 b7) = 4 := by decide
theorem exception3_chunk15 : ∀ b4 b5 b6 b7 : Bool, boundary exception3 (side83 true true true true b4 b5 b6 b7) = 2 ∨ boundary exception3 (side83 true true true true b4 b5 b6 b7) = 4 := by decide
end Chord
