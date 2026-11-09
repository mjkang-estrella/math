import ChordRepresentative
import Mathlib.Data.Fintype.Pi
namespace Chord
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
instance {n} (D : Diagram n) (c : Sides n) (g : Nat) : Decidable (HasGenus D c g) := inferInstanceAs (Decidable (2*g + boundary D c = n+2))

def one : Diagram 1 where
  partner i := ⟨1-i.val, by omega⟩
  involutive i := by apply Fin.ext; dsimp; omega
  noFixed i h := by have := congrArg Fin.val h; dsimp at this; omega

def u2 : Diagram 2 where
  partner i := ⟨if i.val < 2 then 1-i.val else 5-i.val, by split <;> omega⟩
  involutive := by decide
  noFixed := by decide

def r2 : Diagram 2 where
  partner i := ⟨if i.val < 2 then i.val+2 else i.val-2, by split <;> omega⟩
  involutive := by decide
  noFixed := by decide

/-- All 4^3 side assignments are checked in the kernel. -/
theorem r3_boundary_values : ∀ c : Sides 3,
    boundary (r3Block 3 (by decide)) c = 1 ∨ boundary (r3Block 3 (by decide)) c = 3 := by decide

theorem one_boundary_values : ∀ c : Sides 1,
    boundary one c = 1 ∨ boundary one c = 3 := by decide

theorem u2_boundary_values : ∀ c : Sides 2,
    boundary u2 c = 2 ∨ boundary u2 c = 4 := by decide

theorem r2_boundary_values : ∀ c : Sides 2,
    boundary r2 c = 2 ∨ boundary r2 c = 4 := by decide

def maskSides (n m : Nat) : Sides n := fun i => m.testBit i.val

theorem r3_witness_one : HasGenus (r3Block 3 (by decide)) (maskSides 3 0) 1 := by decide
-- The second witness is found independently by the regression script.
theorem r3_witness_two : ∃ m : Fin 64, HasGenus (r3Block 3 (by decide)) (maskSides 3 m.val) 2 := by decide

theorem genusRange_r3 : Range12 (r3Block 3 (by decide)) := by
  intro g
  constructor
  · rintro ⟨c,h⟩
    have hb := r3_boundary_values c
    unfold HasGenus at h
    omega
  · intro h
    rcases h with rfl | rfl
    · exact ⟨_, r3_witness_one⟩
    · obtain ⟨m,hm⟩ := r3_witness_two
      exact ⟨_,hm⟩

/-- Empty-circle terms are both retained. -/
theorem empty_dart (D : Diagram 0) (c : Sides 0) : dartBoundary D c = 2 := by rfl

theorem empty_boundary (D : Diagram 0) (c : Sides 0) : boundary D c = 2 := by rfl

end Chord
