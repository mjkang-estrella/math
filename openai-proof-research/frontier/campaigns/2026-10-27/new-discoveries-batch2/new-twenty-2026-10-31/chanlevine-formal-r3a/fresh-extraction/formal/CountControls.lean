import CountFinal
namespace ChanLevine.CountControls
open scoped Matrix

def sample : Config 3 := ⟨fun k => if k = 0 then 2 else 0,
  fun k => if k = 1 then false else true⟩
theorem sample_test : CycleTest sample := by unfold CycleTest; decide
theorem sample_weight : chipWeight sample = 1 := by decide
theorem sample_rotated : chipWeight (translate 1 sample) = 0 := by decide
theorem wrong_rotation_sign : chipWeight (translate 1 sample) ≠ chipWeight sample - 2 := by decide
theorem wrong_rotor_factor :
    (dominoMatrix (2 : ℤ) 3).det ≠ (3 : ℤ)^2 := by decide
theorem small_lucas :
    ((dominoMatrix (2 : ℤ) 3)^3).trace = -135 := by decide
theorem arithmetic_fixed : ∃ (u : (ZMod 6)ˣ) (b : ℕ),
    (4 : ZMod 6) = (u : ZMod 6)*2 + (b*3 : ℕ) :=
  arithmeticOrbit 6 3 (by decide) (by decide) 2 4 (by decide)
end ChanLevine.CountControls
