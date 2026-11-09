import Cassinian
open Set Complex Cassinian331705
example : y ∈ G := y_mem.1
example : z ∈ G := by norm_num [G, slit, z]
example : (1 : ℂ) ∉ G := by norm_num [G, slit]
example : (1 : ℂ) ∈ frontier G := by rw [frontier_G]; norm_num [slit]
example : (0 : ℂ) ∉ frontier G := by rw [frontier_G]; norm_num [slit]
example : ‖y‖ ^ 2 = 17 := by rw [norm_sq]; norm_num [y]
example : ‖z‖ ^ 2 = 17/4 := by rw [norm_sq]; norm_num [z]
example : (1/2 : ℝ) • y = z := midpoint
example : ¬ StarConvex ℝ (0 : ℂ) (ball G 0 (7/4)) := counterexample.2.2.2.2.2
example : ¬ (y ∉ ball G 0 (7/4)) := by exact not_not.mpr y_mem
example : ¬ (z ∈ ball G 0 (7/4)) := z_not_mem
