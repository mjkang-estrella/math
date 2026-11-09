import ChordFourChunk3_0
import ChordFourChunk3_1
import ChordFourChunk3_2
import ChordFourChunk3_3
namespace Chord
theorem exception3_raw : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool, boundary exception3 (side83 b0 b1 b2 b3 b4 b5 b6 b7) = 2 ∨ boundary exception3 (side83 b0 b1 b2 b3 b4 b5 b6 b7) = 4 := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3
  all_goals first
    | exact exception3_chunk0 b4 b5 b6 b7
    | exact exception3_chunk1 b4 b5 b6 b7
    | exact exception3_chunk2 b4 b5 b6 b7
    | exact exception3_chunk3 b4 b5 b6 b7
    | exact exception3_chunk4 b4 b5 b6 b7
    | exact exception3_chunk5 b4 b5 b6 b7
    | exact exception3_chunk6 b4 b5 b6 b7
    | exact exception3_chunk7 b4 b5 b6 b7
    | exact exception3_chunk8 b4 b5 b6 b7
    | exact exception3_chunk9 b4 b5 b6 b7
    | exact exception3_chunk10 b4 b5 b6 b7
    | exact exception3_chunk11 b4 b5 b6 b7
    | exact exception3_chunk12 b4 b5 b6 b7
    | exact exception3_chunk13 b4 b5 b6 b7
    | exact exception3_chunk14 b4 b5 b6 b7
    | exact exception3_chunk15 b4 b5 b6 b7
theorem exception3_values (c : Sides 4) : boundary exception3 c = 2 ∨ boundary exception3 c = 4 := by
  rw [side83_complete c]
  exact exception3_raw (c ⟨0,by decide⟩) (c ⟨1,by decide⟩) (c ⟨2,by decide⟩) (c ⟨3,by decide⟩) (c ⟨4,by decide⟩) (c ⟨5,by decide⟩) (c ⟨6,by decide⟩) (c ⟨7,by decide⟩)
theorem exception3_one : ∃ c : Sides 4, HasGenus exception3 c 1 := ⟨maskSides 4 7, by decide⟩
theorem exception3_two : ∃ c : Sides 4, HasGenus exception3 c 2 := ⟨maskSides 4 0, by decide⟩
theorem exception3_range : Range12 exception3 := by
  intro g
  constructor
  · rintro ⟨c,h⟩
    have := exception3_values c
    unfold HasGenus at h
    omega
  · rintro (rfl | rfl)
    · exact exception3_one
    · exact exception3_two
end Chord
