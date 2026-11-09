import Moments

namespace Davis

noncomputable section

theorem weighted_reflect (d : ℕ) (x : ℝ) (g : ℕ → ℝ) :
    (∑ i ∈ Finset.range (d + 1), weight d i x * g (d - i)) =
      ∑ i ∈ Finset.range (d + 1), weight d i x * g i := by
  calc
    _ = ∑ i ∈ Finset.range (d + 1), weight d (d - i) x * g (d - i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [weight_reverse (by have := Finset.mem_range.mp hi; omega)]
    _ = _ := by
      simpa only [Nat.add_sub_cancel] using
        Finset.sum_range_reflect (fun i => weight d i x * g i) (d + 1)

theorem weighted_mean (d : ℕ) (x : ℝ) :
    (∑ i ∈ Finset.range (d + 1), weight d i x * (i : ℝ)) = (d : ℝ) / 2 * P d x := by
  have hr := weighted_reflect d x (fun i : ℕ => (i : ℝ))
  have heq : (∑ i ∈ Finset.range (d + 1), weight d i x * ((d - i : ℕ) : ℝ)) =
      (d : ℝ) * P d x - ∑ i ∈ Finset.range (d + 1), weight d i x * (i : ℝ) := by
    calc
      _ = ∑ i ∈ Finset.range (d + 1),
          ((d : ℝ) * weight d i x - weight d i x * (i : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Nat.cast_sub (by have := Finset.mem_range.mp hi; omega)]
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; rfl
  rw [heq] at hr
  linarith

theorem weighted_center_zero (d : ℕ) (x : ℝ) :
    (∑ i ∈ Finset.range (d + 1), weight d i x * ((i : ℝ) - d / 2)) = 0 := by
  calc
    _ = (∑ i ∈ Finset.range (d + 1), weight d i x * (i : ℝ)) -
        (d : ℝ) / 2 * P d x := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [← Finset.sum_mul]
      dsimp [P]
      ring
    _ = 0 := by rw [weighted_mean]; ring

theorem P_step_sum (d : ℕ) (x : ℝ) :
    (∑ i ∈ Finset.range (d + 1), (x - i) ^ 2 * weight d i x) =
      (d + 1 : ℝ) / 2 * P (d + 1) x := by
  calc
    _ = ∑ i ∈ Finset.range (d + 1), (i + 1 : ℝ) * weight (d + 1) (i + 1) x := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [weight_step]
    _ = ∑ i ∈ Finset.range ((d + 1) + 1), weight (d + 1) i x * (i : ℝ) := by
      conv_rhs => rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, mul_zero, add_zero]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    _ = _ := by simpa only [Nat.cast_add, Nat.cast_one] using weighted_mean (d + 1) x

theorem P_step_centered {d : ℕ} {x : ℝ} (hx : (d : ℝ) / 2 < x) :
    (d + 1 : ℝ) / 2 * P (d + 1) x =
      (centralMoment d x 2 + (x - d / 2) ^ 2) * P d x := by
  have hp : P d x ≠ 0 := ne_of_gt (P_pos hx)
  have h2 : centralMoment d x 2 * P d x =
      ∑ i ∈ Finset.range (d + 1), weight d i x * ((i : ℝ) - d / 2) ^ 2 :=
    div_mul_cancel₀ _ hp
  rw [← P_step_sum]
  calc
    _ = ∑ i ∈ Finset.range (d + 1),
        (weight d i x * ((i : ℝ) - d / 2) ^ 2 -
         (2 * (x - d / 2)) * (weight d i x * ((i : ℝ) - d / 2)) +
         (x - d / 2) ^ 2 * weight d i x) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, weighted_center_zero, ← h2]
      simp only [mul_zero, sub_zero]
      dsimp [P]
      ring

theorem remainder_ratio_moment {d : ℕ} {x : ℝ} (hx : (d : ℝ) / 2 < x) :
    -remainder d x / P d x = ((d : ℝ) - 4 * centralMoment d x 2) / (2 * (d + 1)) := by
  have hp : P d x ≠ 0 := ne_of_gt (P_pos hx)
  have hd : (d + 1 : ℝ) ≠ 0 := by positivity
  have hstep := P_step_centered hx
  unfold remainder quotient
  field_simp
  nlinarith

end

end Davis
