import ChordFourChunk0_0
import ChordFourChunk0_1
import ChordFourChunk0_2
import ChordFourChunk0_3
namespace Chord
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000
theorem exception0_raw : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool, boundary exception0 (side80 b0 b1 b2 b3 b4 b5 b6 b7) = 2 ∨ boundary exception0 (side80 b0 b1 b2 b3 b4 b5 b6 b7) = 4 := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3
  · exact exception0_chunk0 b4 b5 b6 b7
  · exact exception0_chunk8 b4 b5 b6 b7
  · exact exception0_chunk4 b4 b5 b6 b7
  · exact exception0_chunk12 b4 b5 b6 b7
  · exact exception0_chunk2 b4 b5 b6 b7
  · exact exception0_chunk10 b4 b5 b6 b7
  · exact exception0_chunk6 b4 b5 b6 b7
  · exact exception0_chunk14 b4 b5 b6 b7
  · exact exception0_chunk1 b4 b5 b6 b7
  · exact exception0_chunk9 b4 b5 b6 b7
  · exact exception0_chunk5 b4 b5 b6 b7
  · exact exception0_chunk13 b4 b5 b6 b7
  · exact exception0_chunk3 b4 b5 b6 b7
  · exact exception0_chunk11 b4 b5 b6 b7
  · exact exception0_chunk7 b4 b5 b6 b7
  · exact exception0_chunk15 b4 b5 b6 b7
theorem exception0_values (c : Sides 4) : boundary exception0 c = 2 ∨ boundary exception0 c = 4 := by
  rw [side80_complete c]
  exact exception0_raw (c ⟨0,by decide⟩) (c ⟨1,by decide⟩) (c ⟨2,by decide⟩) (c ⟨3,by decide⟩) (c ⟨4,by decide⟩) (c ⟨5,by decide⟩) (c ⟨6,by decide⟩) (c ⟨7,by decide⟩)
theorem exception0_one : ∃ c : Sides 4, HasGenus exception0 c 1 := ⟨maskSides 4 0, by decide⟩
theorem exception0_two : ∃ c : Sides 4, HasGenus exception0 c 2 := ⟨maskSides 4 1, by decide⟩
theorem exception0_range : Range12 exception0 := by
  intro g
  constructor
  · rintro ⟨c,h⟩
    have := exception0_values c
    unfold HasGenus at h
    omega
  · rintro (rfl | rfl)
    · exact exception0_one
    · exact exception0_two
end Chord
