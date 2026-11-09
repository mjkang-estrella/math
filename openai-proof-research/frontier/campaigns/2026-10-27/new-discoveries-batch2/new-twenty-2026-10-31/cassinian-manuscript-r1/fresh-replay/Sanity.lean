import Wedge
open Set Complex Cassinian331705 Cassinian331705.Wedge
example : StrictlyStarlike 0 U := strict_U
example : ¬ StrictlyStarlike 0 G := slit_not_strict
example : StarConvex ℝ (0:ℂ) U := star_U
example : y ∈ U := y_ball.1
example : z ∈ U := by norm_num [U,K,z]
example : (1:ℂ) ∉ U := by norm_num [U,K]
example : (0:ℂ) ∉ frontier U := by rw [frontier_eq]; norm_num
example : (⟨2,1/20⟩:ℂ) ∈ frontier U := by rw [frontier_eq]; norm_num
example : ‖y‖^2 = 17 := by norm_num [norm_sq,y]
example : ‖z‖^2 = 17/4 := by norm_num [norm_sq,z]
example : (1/2:ℝ) • y = z := midpoint
example : y ∈ ball U 0 (7/4) ∧ z ∉ ball U 0 (7/4) := ⟨y_ball,z_not_ball⟩
example : ¬ SourceClaim ∧ ¬ SourceClaimStrict := ⟨ordinary_refutation,strict_refutation⟩
example : sSup (insert 0 ((fun p : ℂ => ‖(0:ℂ)-y‖ / (‖(0:ℂ)-p‖ * ‖y-p‖)) '' frontier U)) = cassinian U 0 y := by
  apply infinity_contribution
  · exact ⟨1,boundary 1 (by norm_num) (by norm_num)⟩
  · exact ⟨5/3,by rintro q ⟨p,hp,rfl⟩; exact ratio_y p hp⟩
