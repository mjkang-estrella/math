import C374966Corolla
import Mathlib.Tactic.FieldSimp

/-!
# MathDB 374966 — transmutation of `M_{P_τ}`

`M̄(x,y) = M((1-y)/(1-xy), 1-xy)` computed in `ℚ(x,y) = FractionRing ℚ[x,y]`, equal to the image
of `1 + (-5+5x)y + (8-13x+5x²)y² + (-4+8x-5x²+x³)y³`.
-/

namespace C374966

open Finset MvPolynomial

def tableM : List (List ℤ) := [[1, -5, 8, -4], [0, 5, -13, 8], [0, 0, 5, -5], [0, 0, 0, 1]]

def tMz (i j : ℕ) : ℤ := (tableM.getD i []).getD j 0

def tMq (i j : ℕ) : ℚ := (tMz i j : ℚ)

theorem tMz_vals : tMz 0 0 = 1 ∧ tMz 0 1 = -5 ∧ tMz 0 2 = 8 ∧ tMz 0 3 = -4 ∧
    tMz 1 0 = 0 ∧ tMz 1 1 = 5 ∧ tMz 1 2 = -13 ∧ tMz 1 3 = 8 ∧
    tMz 2 0 = 0 ∧ tMz 2 1 = 0 ∧ tMz 2 2 = 5 ∧ tMz 2 3 = -5 ∧
    tMz 3 0 = 0 ∧ tMz 3 1 = 0 ∧ tMz 3 2 = 0 ∧ tMz 3 3 = 1 := by
  decide

/-- Hand cross-check form `M̄ = 1+(-5+5x)y+(8-13x+5x²)y²+(-4+8x-5x²+x³)y³`. -/
noncomputable def Mbar_lit : Pxy :=
  1 + (-5 + 5 * X 0) * X 1 + (8 - 13 * X 0 + 5 * X 0 ^ 2) * X 1 ^ 2
    + (-4 + 8 * X 0 - 5 * X 0 ^ 2 + X 0 ^ 3) * X 1 ^ 3

theorem tab_M_lit : tab tMq = Mbar_lit := by
  obtain ⟨e00, e01, e02, e03, e10, e11, e12, e13, e20, e21, e22, e23, e30, e31, e32, e33⟩ :=
    tMz_vals
  simp only [tab, tMq, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    e00, e01, e02, e03, e10, e11, e12, e13, e20, e21, e22, e23, e30, e31, e32, e33,
    Int.cast_zero, Int.cast_one, Int.cast_neg, Int.cast_ofNat,
    map_zero, map_one, map_neg, map_ofNat, Mbar_lit]
  ring

/-- The literal rational transmutation of the explicit `M_{P_τ}`. -/
theorem transmute_MP_lit : transmute MP_lit = algebraMap Pxy FracXY Mbar_lit := by
  have hne : (1 : FracXY) - xF * yF ≠ 0 := one_sub_xy_ne
  simp only [transmute, MP_lit, Mbar_lit, map_add, map_sub, map_mul, map_pow, map_one,
    map_ofNat, map_neg, tr_X0, tr_X1]
  field_simp
  ring

/-- `M̄_{P_τ}` of the actual Möbius M-triangle is the image of the explicit table polynomial. -/
theorem transmute_MP : transmute (Mtri P rk) = algebraMap Pxy FracXY (tab tMq) := by
  rw [Mtri_P_lit, transmute_MP_lit, tab_M_lit]

/-- Checked coefficients of `M̄_{P_τ}`: diagonal `1,5,5,1` and `[x y²] = -13`. -/
theorem Mbar_coeffs :
    (tab tMq).coeff (mon 0 0) = 1 ∧ (tab tMq).coeff (mon 1 1) = 5 ∧
    (tab tMq).coeff (mon 2 2) = 5 ∧ (tab tMq).coeff (mon 3 3) = 1 ∧
    (tab tMq).coeff (mon 1 2) = -13 := by
  obtain ⟨e00, -, -, -, -, e11, e12, -, -, -, e22, -, -, -, -, e33⟩ := tMz_vals
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [coeff_tab tMq (i := 0) (j := 0) (by norm_num) (by norm_num), tMq, e00]
    norm_num
  · rw [coeff_tab tMq (i := 1) (j := 1) (by norm_num) (by norm_num), tMq, e11]
    norm_num
  · rw [coeff_tab tMq (i := 2) (j := 2) (by norm_num) (by norm_num), tMq, e22]
    norm_num
  · rw [coeff_tab tMq (i := 3) (j := 3) (by norm_num) (by norm_num), tMq, e33]
    norm_num
  · rw [coeff_tab tMq (i := 1) (j := 2) (by norm_num) (by norm_num), tMq, e12]
    norm_num

end C374966
