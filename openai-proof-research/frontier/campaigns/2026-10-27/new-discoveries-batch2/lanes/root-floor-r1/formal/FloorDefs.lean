import Mathlib
set_option autoImplicit false
namespace FloorRigidity

noncomputable def sourceValue (a : ℝ) (n : ℕ) : ℤ :=
  ⌊a^2 * n⌋ - ⌊a * (⌊a*n⌋ : ℤ)⌋

def SourceClaim (a : ℝ) : Prop := ∀ n : ℕ, 0 < n → sourceValue a n = 1

theorem source_value_one_iff (a : ℝ) (n : ℕ) : sourceValue a n = 1 ↔
    a * Int.fract (a*n) - 1 ≤ Int.fract (a^2*n) ∧
    Int.fract (a^2*n) < a * Int.fract (a*n) := by
  have hring : a * (⌊a*n⌋ : ℤ) =
      (⌊a^2*n⌋ : ℤ) + Int.fract (a^2*n) - a * Int.fract (a*n) := by
    simp only [Int.fract]
    ring
  constructor
  · intro h
    have he : ⌊a * (⌊a*n⌋ : ℤ)⌋ = ⌊a^2*n⌋ - 1 := by
      dsimp [sourceValue] at h
      omega
    have hh := (Int.floor_eq_iff).mp he
    simp only [Int.cast_sub, Int.cast_one] at hh
    rw [hring] at hh
    constructor <;> linarith [hh.1, hh.2]
  · rintro ⟨hlo, hhi⟩
    have he : ⌊a * (⌊a*n⌋ : ℤ)⌋ = ⌊a^2*n⌋ - 1 := by
      apply Int.floor_eq_iff.mpr
      simp only [Int.cast_sub, Int.cast_one]
      rw [hring]
      constructor <;> linarith
    dsimp [sourceValue]
    omega

theorem golden_ratio_suffices : SourceClaim Real.goldenRatio := by
  intro n hn
  apply (source_value_one_iff _ _).mpr
  have hφ := Real.one_lt_goldenRatio
  have hφ2 := Real.goldenRatio_lt_two
  have hu0 : 0 < Int.fract (Real.goldenRatio*n) := by
    apply Int.fract_pos.mpr
    intro hz
    exact (Real.goldenRatio_irrational.mul_natCast (by omega)).ne_int _ hz
  have hu1 := Int.fract_lt_one (Real.goldenRatio*n)
  have hv : Int.fract (Real.goldenRatio^2*n) = Int.fract (Real.goldenRatio*n) := by
    rw [Real.goldenRatio_sq]
    have he : (Real.goldenRatio+1)*(n:ℝ) = Real.goldenRatio*n + (n:ℤ) := by
      push_cast
      ring
    rw [he, Int.fract_add_intCast]
  rw [hv]
  constructor <;> nlinarith

end FloorRigidity
