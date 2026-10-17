/- Copyright 2026 Myeongjin Kang. MIT. Semantic controls; not O217 proof. -/
import O217
namespace O217Controls
open O217

def edge01 : Edge 2 := ⟨(0, 1), by decide⟩
def plus : Fin 2 → Bool := fun _ => false

theorem wrong_gauge_sign_rejected :
    edgeSpin (flipSpin 0 plus) edge01 ≠ edgeSpin plus edge01 := by
  norm_num [edgeSpin, flipSpin, spinSign, plus, edge01]

theorem incident_disorder_negated : flipDisorder 0 (fun _ : Edge 2 => (3 : ℝ)) edge01 = -3 := by
  norm_num [flipDisorder, incident, edge01]

theorem dropped_square_rejected :
    (2 : ℝ)^2 - 1^2 * 1^2 - 1 * 0 * 1^3 ≠ 2 * 1 * 1 * (2 - 1*1 - 0*1^2/2) := by
  norm_num

theorem bootstrap_small_constant_premise :
    (1 : ℝ) ≤ 0 + (1/2) * Real.sqrt 1 + 1/2 := by norm_num

theorem bootstrap_small_constant_rejected :
    ¬ (Real.sqrt (1 : ℝ) ≤ Real.sqrt 0 + 1/2) := by norm_num

theorem bootstrap_negative_constant_premise :
    (0 : ℝ) ≤ 4 + (-4) * Real.sqrt 0 + (-4) := by norm_num

theorem bootstrap_negative_constant_rejected :
    ¬ (Real.sqrt (0 : ℝ) ≤ Real.sqrt 4 + (-4) + Real.sqrt (-4)) := by norm_num

theorem centering_term_required : |(1 : ℝ) - 1^2 - 1| > |1-1| := by norm_num
end O217Controls
