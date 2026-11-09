import Algebra333569
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.Compact

namespace MathDB333569
noncomputable section
set_option maxHeartbeats 800000
open Set

def gapEntropy (r : ℝ) : ℝ := Real.binEntropy ((1-r)/2)
def diagonalTerm (l : ℝ) (n : ℕ) : ℝ :=
  (1/2:ℝ)^(n+1) * (gapEntropy (l^(n+1)) - gapEntropy l)
def diagonal (l : ℝ) : ℝ := ∑' n : ℕ, diagonalTerm l n

theorem pow_le_base {l : ℝ} (hl : l ∈ Icc 0 1) (n : ℕ) : l^(n+1) ≤ l := by
  rw [pow_succ]
  exact mul_le_of_le_one_left hl.1 (pow_le_one₀ hl.1 hl.2)

theorem gapEntropy_nonneg {l : ℝ} (hl : l ∈ Icc 0 1) : 0 ≤ gapEntropy l := by
  apply Real.binEntropy_nonneg <;> linarith [hl.1, hl.2]

theorem gapEntropy_le (l : ℝ) : gapEntropy l ≤ Real.log 2 := Real.binEntropy_le_log_two

theorem gapEntropy_anti : AntitoneOn gapEntropy (Icc 0 1) := by
  intro x hx y hy hxy
  apply Real.binEntropy_strictMonoOn.monotoneOn
  · constructor <;> linarith [hy.1, hy.2]
  · constructor <;> linarith [hx.1, hx.2]
  · linarith

theorem diagonalTerm_nonneg {l : ℝ} (hl : l ∈ Icc 0 1) (n : ℕ) :
    0 ≤ diagonalTerm l n := by
  apply mul_nonneg (by positivity)
  exact sub_nonneg.mpr (gapEntropy_anti
    ⟨pow_nonneg hl.1 _, pow_le_one₀ hl.1 hl.2⟩ hl (pow_le_base hl n))

theorem diagonalTerm_bound {l : ℝ} (hl : l ∈ Icc 0 1) (n : ℕ) :
    ‖diagonalTerm l n‖ ≤ (1/2:ℝ)^(n+1) * Real.log 2 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (diagonalTerm_nonneg hl n)]
  exact mul_le_mul_of_nonneg_left
    (by linarith [gapEntropy_le (l^(n+1)), gapEntropy_nonneg hl]) (by positivity)

theorem geometricMajorant_summable :
    Summable (fun n : ℕ => (1/2:ℝ)^(n+1) * Real.log 2) := by
  have h : Summable (fun n : ℕ => (1/2:ℝ)^n) := summable_geometric_of_norm_lt_one (by norm_num)
  simpa only [pow_succ, mul_assoc] using (h.mul_right (1/2)).mul_right (Real.log 2)

theorem diagonal_summable {l : ℝ} (hl : l ∈ Icc 0 1) : Summable (diagonalTerm l) :=
  geometricMajorant_summable.of_norm_bounded (diagonalTerm_bound hl)

theorem diagonal_continuousOn : ContinuousOn diagonal (Icc 0 1) := by
  apply continuousOn_tsum (u := fun n : ℕ => (1/2:ℝ)^(n+1)*Real.log 2)
  · intro n
    unfold diagonalTerm gapEntropy
    fun_prop
  · exact geometricMajorant_summable
  · intro n l hl
    exact diagonalTerm_bound hl n

theorem diagonal_zero : diagonal 0 = 0 := by
  simp [diagonal, diagonalTerm]
theorem diagonal_one : diagonal 1 = 0 := by
  simp [diagonal, diagonalTerm]

theorem diagonal_pos {l : ℝ} (hl : l ∈ Ioo 0 1) : 0 < diagonal l := by
  apply (diagonal_summable ⟨le_of_lt hl.1, le_of_lt hl.2⟩).tsum_pos
    (diagonalTerm_nonneg ⟨le_of_lt hl.1, le_of_lt hl.2⟩) 1
  apply mul_pos (by positivity)
  apply sub_pos.mpr
  apply Real.binEntropy_strictMonoOn
  · constructor <;> linarith [hl.1, hl.2]
  · constructor <;> nlinarith [sq_nonneg l, mul_pos hl.1 (by linarith [hl.2] : 0 < 1-l)]
  · nlinarith [mul_pos hl.1 (by linarith [hl.2] : 0 < 1-l)]

/-- A proved compact maximum of the actual diagonal entropy series, still not the source endpoint. -/
theorem diagonal_has_interior_max :
    ∃ l ∈ Ioo (0:ℝ) 1, ∀ r ∈ Icc (0:ℝ) 1, diagonal r ≤ diagonal l := by
  obtain ⟨l, hl, hm⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0:ℝ) 1).Nonempty from ⟨0, by constructor <;> norm_num⟩)
    diagonal_continuousOn
  have hp := diagonal_pos (show (1/2:ℝ) ∈ Ioo 0 1 by constructor <;> norm_num)
  have hlp : 0 < diagonal l := lt_of_lt_of_le hp (hm (by constructor <;> norm_num))
  have h0 : l ≠ 0 := by intro h; rw [h, diagonal_zero] at hlp; exact lt_irrefl _ hlp
  have h1 : l ≠ 1 := by intro h; rw [h, diagonal_one] at hlp; exact lt_irrefl _ hlp
  exact ⟨l, ⟨lt_of_le_of_ne hl.1 (Ne.symm h0), lt_of_le_of_ne hl.2 h1⟩, hm⟩

#print axioms diagonal_continuousOn
#print axioms diagonal_pos
#print axioms diagonal_has_interior_max
end
end MathDB333569
