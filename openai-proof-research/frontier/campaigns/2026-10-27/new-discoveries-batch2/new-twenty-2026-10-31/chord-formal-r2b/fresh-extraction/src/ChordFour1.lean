import ChordFourChunk1_0
import ChordFourChunk1_1
import ChordFourChunk1_2
import ChordFourChunk1_3
namespace Chord
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000
theorem exception1_raw : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool, boundary exception1 (side81 b0 b1 b2 b3 b4 b5 b6 b7) = 2 ∨ boundary exception1 (side81 b0 b1 b2 b3 b4 b5 b6 b7) = 4 := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3
  · exact exception1_chunk0 b4 b5 b6 b7
  · exact exception1_chunk8 b4 b5 b6 b7
  · exact exception1_chunk4 b4 b5 b6 b7
  · exact exception1_chunk12 b4 b5 b6 b7
  · exact exception1_chunk2 b4 b5 b6 b7
  · exact exception1_chunk10 b4 b5 b6 b7
  · exact exception1_chunk6 b4 b5 b6 b7
  · exact exception1_chunk14 b4 b5 b6 b7
  · exact exception1_chunk1 b4 b5 b6 b7
  · exact exception1_chunk9 b4 b5 b6 b7
  · exact exception1_chunk5 b4 b5 b6 b7
  · exact exception1_chunk13 b4 b5 b6 b7
  · exact exception1_chunk3 b4 b5 b6 b7
  · exact exception1_chunk11 b4 b5 b6 b7
  · exact exception1_chunk7 b4 b5 b6 b7
  · exact exception1_chunk15 b4 b5 b6 b7
theorem exception1_values (c : Sides 4) : boundary exception1 c = 2 ∨ boundary exception1 c = 4 := by
  rw [side81_complete c]
  exact exception1_raw (c ⟨0,by decide⟩) (c ⟨1,by decide⟩) (c ⟨2,by decide⟩) (c ⟨3,by decide⟩) (c ⟨4,by decide⟩) (c ⟨5,by decide⟩) (c ⟨6,by decide⟩) (c ⟨7,by decide⟩)
theorem exception1_one : ∃ c : Sides 4, HasGenus exception1 c 1 := ⟨maskSides 4 5, by decide⟩
theorem exception1_two : ∃ c : Sides 4, HasGenus exception1 c 2 := ⟨maskSides 4 0, by decide⟩
theorem exception1_range : Range12 exception1 := by
  intro g
  constructor
  · rintro ⟨c,h⟩
    have := exception1_values c
    unfold HasGenus at h
    omega
  · rintro (rfl | rfl)
    · exact exception1_one
    · exact exception1_two
end Chord
