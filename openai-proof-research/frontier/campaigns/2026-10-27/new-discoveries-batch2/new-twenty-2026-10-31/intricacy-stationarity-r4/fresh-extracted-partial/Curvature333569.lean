import Algebra333569
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace MathDB333569
noncomputable section
open Set

def logOdds (r : ℝ) : ℝ := Real.log (1+r) - Real.log (1-r)
def transverseCoeff (r : ℝ) : ℝ :=
  -(1-r)/2 * logOdds r - (1-r)/(2*(1+r))
def coeffSlope (r : ℝ) : ℝ := logOdds r / 2 - r/(1+r)^2

theorem logOdds_eq {r : ℝ} (hr : r ∈ Ioo (-1) 1) :
    logOdds r = Real.log ((1+r)/(1-r)) := by
  rw [Real.log_div (by linarith [hr.1] : 1+r ≠ 0) (by linarith [hr.2] : 1-r ≠ 0)]
  rfl

theorem logOdds_hasDerivAt {r : ℝ} (hr : r ∈ Ioo (-1) 1) :
    HasDerivAt logOdds (2/((1-r)*(1+r))) r := by
  have ha : 1+r ≠ 0 := by linarith [hr.1]
  have hb : 1-r ≠ 0 := by linarith [hr.2]
  convert (((hasDerivAt_const r (1:ℝ)).add (hasDerivAt_id r)).log ha).sub
    (((hasDerivAt_const r (1:ℝ)).sub (hasDerivAt_id r)).log hb) using 1 <;>
    first | rfl | (dsimp; field_simp; ring)

theorem coeffSlope_hasDerivAt {r : ℝ} (hr : r ∈ Ioo (-1) 1) :
    HasDerivAt coeffSlope (4*r/((1-r)*(1+r)^3)) r := by
  have ha : 1+r ≠ 0 := by linarith [hr.1]
  have hb : 1-r ≠ 0 := by linarith [hr.2]
  convert ((logOdds_hasDerivAt hr).div_const 2).sub
    ((hasDerivAt_id r).div
      (((hasDerivAt_const r (1:ℝ)).add (hasDerivAt_id r)).pow 2)
      (pow_ne_zero 2 ha)) using 1 <;>
    first | rfl | (dsimp; field_simp; ring)

theorem transverseCoeff_hasDerivAt {r : ℝ} (hr : r ∈ Ioo (-1) 1) :
    HasDerivAt transverseCoeff (coeffSlope r) r := by
  have ha : 1+r ≠ 0 := by linarith [hr.1]
  have hb : 1-r ≠ 0 := by linarith [hr.2]
  convert (((((hasDerivAt_const r (1:ℝ)).sub (hasDerivAt_id r)).neg).div_const 2).mul
    (logOdds_hasDerivAt hr)).sub
    (((hasDerivAt_const r (1:ℝ)).sub (hasDerivAt_id r)).div
      (((hasDerivAt_const r (1:ℝ)).add (hasDerivAt_id r)).const_mul 2)
      (mul_ne_zero (by norm_num) ha)) using 1
  · rfl
  · dsimp [coeffSlope]
    field_simp
    ring

theorem coeffSlope_strictMonoOn : StrictMonoOn coeffSlope (Ico 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ico 0 1)
  · intro r hr
    exact (coeffSlope_hasDerivAt ⟨by linarith [hr.1], hr.2⟩).continuousAt.continuousWithinAt
  · intro r hr
    rw [interior_Ico] at hr
    rw [(coeffSlope_hasDerivAt ⟨by linarith [hr.1], hr.2⟩).deriv]
    exact div_pos (by linarith [hr.1])
      (mul_pos (by linarith [hr.2]) (pow_pos (by linarith [hr.1]) 3))

theorem coeffSlope_pos {r : ℝ} (hr : r ∈ Ioo 0 1) : 0 < coeffSlope r := by
  have h := coeffSlope_strictMonoOn (show (0:ℝ) ∈ Ico 0 1 by constructor <;> norm_num)
    ⟨le_of_lt hr.1, hr.2⟩ hr.1
  simpa [coeffSlope, logOdds] using h

theorem transverseCoeff_strictMonoOn : StrictMonoOn transverseCoeff (Ico 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ico 0 1)
  · intro r hr
    exact (transverseCoeff_hasDerivAt ⟨by linarith [hr.1], hr.2⟩).continuousAt.continuousWithinAt
  · intro r hr
    rw [interior_Ico] at hr
    rw [(transverseCoeff_hasDerivAt ⟨by linarith [hr.1], hr.2⟩).deriv]
    exact coeffSlope_pos hr

theorem transverseCoeff_power_le {l : ℝ} (hl : l ∈ Ioo 0 1) {n : ℕ} (hn : 1 ≤ n) :
    transverseCoeff (l^n) ≤ transverseCoeff l := by
  apply transverseCoeff_strictMonoOn.monotoneOn
    ⟨le_of_lt (pow_pos hl.1 n), pow_lt_one₀ (le_of_lt hl.1) hl.2 (by omega)⟩
    ⟨le_of_lt hl.1, hl.2⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [pow_add, pow_one]
  exact mul_le_of_le_one_right (le_of_lt hl.1) (pow_le_one₀ (le_of_lt hl.1) (le_of_lt hl.2))

theorem transverseCoeff_square_lt {l : ℝ} (hl : l ∈ Ioo 0 1) :
    transverseCoeff (l^2) < transverseCoeff l := by
  apply transverseCoeff_strictMonoOn
    ⟨le_of_lt (pow_pos hl.1 2), pow_lt_one₀ (le_of_lt hl.1) hl.2 (by omega)⟩
    ⟨le_of_lt hl.1, hl.2⟩
  nlinarith [mul_pos hl.1 (by linarith [hl.2] : 0 < 1-l)]

#print axioms transverseCoeff_hasDerivAt
#print axioms transverseCoeff_strictMonoOn
#print axioms transverseCoeff_power_le
#print axioms transverseCoeff_square_lt
end
end MathDB333569
