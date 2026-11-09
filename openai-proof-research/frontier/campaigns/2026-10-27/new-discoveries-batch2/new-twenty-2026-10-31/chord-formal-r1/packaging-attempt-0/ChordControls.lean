import ChordSmall
namespace Chord

theorem negative_wrong_euler_offset :
    ¬ (2*1 + boundary (r3Block 3 (by decide)) (maskSides 3 0) = 3+1) := by decide

theorem negative_drop_empty_circle :
    cycles 2 (fun i => nextSame (maskSides 1 0) (mate one i)) ≠ boundary one (maskSides 1 0) := by decide

/-- Replacing the triangle by an isolated-pair diagram already fails at the base size. -/
def isolated3 : Diagram 3 where
  partner i := ⟨if i.val % 2 = 0 then i.val+1 else i.val-1, by split <;> omega⟩
  involutive := by decide
  noFixed := by decide

theorem negative_wrong_representative : ¬Range12 isolated3 := by
  intro h
  have zero : genusRange isolated3 0 := ⟨maskSides 3 0, by decide⟩
  have := (h 0).mp zero
  omega
end Chord
