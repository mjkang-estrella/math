import SourceDefs

open Filter Topology

namespace Schmidlin

theorem logGamma_add_one {z : ℝ} (hz : 0 < z) :
    Real.log (Real.Gamma (z+1)) = Real.log (Real.Gamma z)+Real.log z := by
  rw [Real.Gamma_add_one (ne_of_gt hz), Real.log_mul (ne_of_gt hz)
    (ne_of_gt (Real.Gamma_pos_of_pos hz))]
  ring

theorem gammaError_nat_succ (n : ℕ) :
    gammaError (n+1) = Real.log (Stirling.stirlingSeq (n+1))-Real.log Real.pi/2 := by
  have hn : 0 < (n:ℝ)+1 := by positivity
  have hg := Real.Gamma_pos_of_pos hn
  have he := logGamma_add_one hn
  have hf := Real.Gamma_nat_eq_factorial (n+1)
  rw [Stirling.log_stirlingSeq_formula]
  unfold gammaError
  push_cast at he hf ⊢
  rw [hf] at he
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt hn),
    Real.log_div (ne_of_gt hn) (ne_of_gt (Real.exp_pos 1)), Real.log_exp,
    Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt Real.pi_pos)]
  linarith

theorem gammaError_nat_tendsto :
    Tendsto (fun n : ℕ => gammaError (n+1)) atTop (nhds 0) := by
  have h := (Real.continuousAt_log (by positivity : Real.sqrt Real.pi ≠ 0)).tendsto.comp
    (Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1))
  have hs : Real.log (Real.sqrt Real.pi) = Real.log Real.pi/2 := by
    rw [Real.log_sqrt Real.pi_pos.le]
  simpa only [Function.comp_def, gammaError_nat_succ, hs, sub_self]
    using h.sub_const (Real.log Real.pi/2)

end Schmidlin
