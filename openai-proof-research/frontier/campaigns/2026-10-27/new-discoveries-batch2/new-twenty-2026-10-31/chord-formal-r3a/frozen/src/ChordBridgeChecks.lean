import ChordSmall
namespace Chord
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

theorem bridge_one : ∀ c : Sides 1, boundary one c = dartBoundary one c := by decide

theorem bridge_u2 : ∀ c : Sides 2, boundary u2 c = dartBoundary u2 c := by decide

theorem bridge_r2 : ∀ c : Sides 2, boundary r2 c = dartBoundary r2 c := by decide

theorem bridge_nested2 : ∀ c : Sides 2, boundary nested2 c = dartBoundary nested2 c := by decide

theorem bridge_r3 : ∀ c : Sides 3,
    boundary (r3Block 3 (by decide)) c = dartBoundary (r3Block 3 (by decide)) c := by decide

theorem bridge_all_one (D : Diagram 1) (c : Sides 1) : boundary D c = dartBoundary D c := by
  rw [classify_one D]
  exact bridge_one c

theorem bridge_all_two (D : Diagram 2) (c : Sides 2) : boundary D c = dartBoundary D c := by
  rcases classify_two D with h | h | h <;> subst D
  · exact bridge_u2 c
  · exact bridge_r2 c
  · exact bridge_nested2 c
end Chord
