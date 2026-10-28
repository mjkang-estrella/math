import GammaDefs

/-!
# Literal gamma-ratio level equivalence

For `x > 0`, `y > 0`, `c > 0`:

    logDefect x (x + y) = log c  <->  Gamma y * Gamma (y + 2 * x) / Gamma (y + x) ^ 2 = c,

proved by rewriting the defect into a single logarithm via `Real.log_mul`,
`Real.log_div`, `Real.log_pow` (all `Gamma` arguments are positive by
`Real.Gamma_pos_of_pos`) and injectivity of `Real.log` on positive reals
(`Real.strictMono_log` / exponentiation).

Also: `SourceLevel c x y` is equivalent to `0 < y` together with the defect-level
equation, so the implicit curve can be characterized at either level literally.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section
open Set Filter Topology

namespace GammaLevel

/-- Shifted shape of the defect at `s = x + y`: the three Gamma arguments are
exactly `y`, `y + 2 * x` and `y + x`. -/
theorem logDefect_shift (x y : ℝ) :
    logDefect x (x + y) = Real.log (Real.Gamma y) + Real.log (Real.Gamma (y + 2 * x)) -
      2 * Real.log (Real.Gamma (y + x)) := by
  have e0 : (x + y) - x = y := by ring
  have e1 : (x + y) + x = y + 2 * x := by ring
  have e2 : x + y = y + x := by ring
  show Real.log (Real.Gamma ((x + y) - x)) + Real.log (Real.Gamma ((x + y) + x)) -
    2 * Real.log (Real.Gamma (x + y)) = _
  rw [e0, e1, e2]

/-- **Literal ratio equivalence.** For `x > 0`, `y > 0`, `c > 0` the defect-level
equation holds iff the literal Gamma ratio equals `c`. -/
theorem logDefect_eq_log_iff_ratio {x y c : ℝ} (hx : 0 < x) (hy : 0 < y) (hc : 0 < c) :
    logDefect x (x + y) = Real.log c ↔
      Real.Gamma y * Real.Gamma (y + 2 * x) / Real.Gamma (y + x) ^ 2 = c := by
  have hGy : 0 < Real.Gamma y := Real.Gamma_pos_of_pos hy
  have hG2 : 0 < Real.Gamma (y + 2 * x) := Real.Gamma_pos_of_pos (by linarith)
  have hG1 : 0 < Real.Gamma (y + x) := Real.Gamma_pos_of_pos (by linarith)
  have hlogform : logDefect x (x + y)
      = Real.log (Real.Gamma y * Real.Gamma (y + 2 * x) / Real.Gamma (y + x) ^ 2) := by
    rw [logDefect_shift, Real.log_div
      (mul_ne_zero (ne_of_gt hGy) (ne_of_gt hG2)) (ne_of_gt (pow_pos hG1 2)),
      Real.log_mul (ne_of_gt hGy) (ne_of_gt hG2), Real.log_pow]
    ring
  constructor
  · intro h
    have h' : Real.log (Real.Gamma y * Real.Gamma (y + 2 * x) / Real.Gamma (y + x) ^ 2)
        = Real.log c := by rw [← hlogform, h]
    have hposA : 0 < Real.Gamma y * Real.Gamma (y + 2 * x) / Real.Gamma (y + x) ^ 2 := by
      positivity
    exact Real.log_injOn_pos (mem_Ioi.2 hposA) (mem_Ioi.2 hc) h'
  · intro h
    rw [hlogform, h]

/-- The source-level proposition is equivalent to positivity of `y` together with the
defect-level equation, so the implicit curve can be characterized at either level. -/
theorem sourceLevel_iff_defect {c x y : ℝ} (hx : 0 < x) (hc : 0 < c) :
    SourceLevel c x y ↔ 0 < y ∧ logDefect x (x + y) = Real.log c := by
  constructor
  · rintro ⟨hy, hr⟩
    exact ⟨hy, (logDefect_eq_log_iff_ratio hx hy hc).mpr hr⟩
  · rintro ⟨hy, hd⟩
    exact ⟨hy, (logDefect_eq_log_iff_ratio hx hy hc).mp hd⟩

end GammaLevel
