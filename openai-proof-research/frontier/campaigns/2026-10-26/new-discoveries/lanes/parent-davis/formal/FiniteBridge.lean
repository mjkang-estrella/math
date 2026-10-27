import FiniteCheck

namespace Davis

theorem source_bound_of_certificate {d : ℕ} {x : ℝ} (hd : 5 ≤ d)
    (hx : ((d : ℝ) + Real.sqrt (d + 2)) / 2 ≤ x) (hc : certificateCheck d = true) :
    (199 / 200 : ℝ) * (d - 2) / (2 * x + d - 2) < -remainder d x / P d x := by
  have hdr : (5 : ℝ) ≤ d := by exact_mod_cast hd
  have hsqrt : 0 < Real.sqrt (d + 2 : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hhalf : (d : ℝ) / 2 < x := by linarith
  have hp : 0 < P d x := P_pos hhalf
  have hden : 0 < 2 * x + d - 2 := by linarith
  have heval := certificate_implies_positive hc hx
  rw [coeffEval_inequality] at heval
  have hscale : 0 < 400 * (d + 1 : ℝ) * (Nat.factorial d : ℝ) := by positivity
  have hdiff := (mul_pos_iff_of_pos_left hscale).mp heval
  apply (div_lt_div_iff₀ hden hp).mpr
  unfold remainder
  nlinarith

end Davis
