import ChordFourChunk2_0
import ChordFourChunk2_1
import ChordFourChunk2_2
import ChordFourChunk2_3
namespace Chord
theorem exception2_raw : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool, boundary exception2 (side82 b0 b1 b2 b3 b4 b5 b6 b7) = 2 ∨ boundary exception2 (side82 b0 b1 b2 b3 b4 b5 b6 b7) = 4 := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3
  all_goals first
    | exact exception2_chunk0 b4 b5 b6 b7
    | exact exception2_chunk1 b4 b5 b6 b7
    | exact exception2_chunk2 b4 b5 b6 b7
    | exact exception2_chunk3 b4 b5 b6 b7
    | exact exception2_chunk4 b4 b5 b6 b7
    | exact exception2_chunk5 b4 b5 b6 b7
    | exact exception2_chunk6 b4 b5 b6 b7
    | exact exception2_chunk7 b4 b5 b6 b7
    | exact exception2_chunk8 b4 b5 b6 b7
    | exact exception2_chunk9 b4 b5 b6 b7
    | exact exception2_chunk10 b4 b5 b6 b7
    | exact exception2_chunk11 b4 b5 b6 b7
    | exact exception2_chunk12 b4 b5 b6 b7
    | exact exception2_chunk13 b4 b5 b6 b7
    | exact exception2_chunk14 b4 b5 b6 b7
    | exact exception2_chunk15 b4 b5 b6 b7
theorem exception2_values (c : Sides 4) : boundary exception2 c = 2 ∨ boundary exception2 c = 4 := by
  rw [side82_complete c]
  exact exception2_raw (c ⟨0,by decide⟩) (c ⟨1,by decide⟩) (c ⟨2,by decide⟩) (c ⟨3,by decide⟩) (c ⟨4,by decide⟩) (c ⟨5,by decide⟩) (c ⟨6,by decide⟩) (c ⟨7,by decide⟩)
theorem exception2_one : ∃ c : Sides 4, HasGenus exception2 c 1 := ⟨maskSides 4 0, by decide⟩
theorem exception2_two : ∃ c : Sides 4, HasGenus exception2 c 2 := ⟨maskSides 4 1, by decide⟩
theorem exception2_range : Range12 exception2 := by
  intro g
  constructor
  · rintro ⟨c,h⟩
    have := exception2_values c
    unfold HasGenus at h
    omega
  · rintro (rfl | rfl)
    · exact exception2_one
    · exact exception2_two
end Chord
