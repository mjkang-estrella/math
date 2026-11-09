import Weights
import Stationarity
import TailBound

namespace Davis

noncomputable section

def centralMoment (d : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  (∑ i ∈ Finset.range (d + 1), weight d i x * ((i : ℝ) - d / 2) ^ k) / P d x

theorem raw_moment_identity (d : ℕ) (x : ℝ) :
    2 * (∑ i ∈ Finset.range (d + 1), weight d i x * ((i : ℝ) - d / 2) ^ 4) +
      momentCoefficient d (x - d / 2) *
        (∑ i ∈ Finset.range (d + 1), weight d i x * ((i : ℝ) - d / 2) ^ 2) =
      (d : ℝ) / 2 * (x - d / 2) ^ 2 * P d x := by
  let L := fun i : ℕ => ((d - i : ℕ) : ℝ) * (x - i) ^ 2 * weight d i x
  let M := fun i : ℕ => (i : ℝ) * (x - d + i) ^ 2 * weight d i x
  let f := fun i : ℕ => ((i : ℝ) - d / 2) ^ 2
  have hL : L d = 0 := by simp [L]
  have hM : M 0 = 0 := by simp [M]
  have hb : ∀ i < d, L i = M (i + 1) := by
    intro i hi
    simpa only [L, M, Nat.cast_add, Nat.cast_one] using weight_balance hi x
  have hs := finite_stationarity d L M f hL hM hb
  have hpoint : ∀ i ∈ Finset.range (d + 1),
      L i * (f (i + 1) - f i) + M i * (f (i - 1) - f i) =
        -2 * (2 * (weight d i x * ((i : ℝ) - d / 2) ^ 4) +
          momentCoefficient d (x - d / 2) * (weight d i x * ((i : ℝ) - d / 2) ^ 2) -
          (d : ℝ) / 2 * (x - d / 2) ^ 2 * weight d i x) := by
    intro i hi
    have hid : i ≤ d := by have := Finset.mem_range.mp hi; omega
    by_cases hi0 : i = 0
    · subst i
      simp only [L, M, f, Nat.sub_zero, Nat.cast_zero, Nat.zero_add, Nat.cast_one,
        Nat.zero_sub, zero_mul, add_zero]
      dsimp [momentCoefficient]
      ring
    · have hip : 1 ≤ i := by omega
      simp only [L, M, f, Nat.cast_sub hid, Nat.cast_sub hip, Nat.cast_add, Nat.cast_one]
      dsimp [momentCoefficient]
      ring
  have hsum := Finset.sum_congr rfl hpoint
  rw [hs, ← Finset.mul_sum] at hsum
  have hzero : (∑ i ∈ Finset.range (d + 1),
       (2 * (weight d i x * ((i : ℝ) - d / 2) ^ 4) +
        momentCoefficient d (x - d / 2) * (weight d i x * ((i : ℝ) - d / 2) ^ 2) -
        (d : ℝ) / 2 * (x - d / 2) ^ 2 * weight d i x)) = 0 := by linarith
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum] at hzero
  dsimp [P] at ⊢
  linarith

theorem moment_identity {d : ℕ} {x : ℝ} (hx : (d : ℝ) / 2 < x) :
    2 * centralMoment d x 4 + momentCoefficient d (x - d / 2) * centralMoment d x 2 =
      (d : ℝ) / 2 * (x - d / 2) ^ 2 := by
  have hp : P d x ≠ 0 := ne_of_gt (P_pos hx)
  have h2 : centralMoment d x 2 * P d x =
      ∑ i ∈ Finset.range (d + 1), weight d i x * ((i : ℝ) - d / 2) ^ 2 :=
    div_mul_cancel₀ _ hp
  have h4 : centralMoment d x 4 * P d x =
      ∑ i ∈ Finset.range (d + 1), weight d i x * ((i : ℝ) - d / 2) ^ 4 :=
    div_mul_cancel₀ _ hp
  have hraw := raw_moment_identity d x
  have hzero : (2 * centralMoment d x 4 +
      momentCoefficient d (x - d / 2) * centralMoment d x 2 -
      (d : ℝ) / 2 * (x - d / 2) ^ 2) * P d x = 0 := by
    rw [sub_mul, add_mul, mul_assoc 2, mul_assoc (momentCoefficient d (x - d / 2)), h2, h4]
    linarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right hp)

theorem centralMoment_two_nonneg (d : ℕ) (x : ℝ) : 0 ≤ centralMoment d x 2 := by
  unfold centralMoment P
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (weight_nonneg d i x) (sq_nonneg _)
  · exact Finset.sum_nonneg (fun i hi => weight_nonneg d i x)

theorem moment_four_ge_sq {d : ℕ} {x : ℝ} (hx : (d : ℝ) / 2 < x) :
    (centralMoment d x 2) ^ 2 ≤ centralMoment d x 4 := by
  let V := centralMoment d x 2
  have hp : 0 < P d x := P_pos hx
  have h2 : V * P d x =
      ∑ i ∈ Finset.range (d + 1), weight d i x * ((i : ℝ) - d / 2) ^ 2 :=
    div_mul_cancel₀ _ (ne_of_gt hp)
  have h4 : centralMoment d x 4 * P d x =
      ∑ i ∈ Finset.range (d + 1), weight d i x * ((i : ℝ) - d / 2) ^ 4 :=
    div_mul_cancel₀ _ (ne_of_gt hp)
  have hnn : 0 ≤ ∑ i ∈ Finset.range (d + 1),
      weight d i x * (((i : ℝ) - d / 2) ^ 2 - V) ^ 2 := by
    exact Finset.sum_nonneg (fun i hi => mul_nonneg (weight_nonneg d i x) (sq_nonneg _))
  have heq : (∑ i ∈ Finset.range (d + 1),
      weight d i x * (((i : ℝ) - d / 2) ^ 2 - V) ^ 2) =
      centralMoment d x 4 * P d x - 2 * V * (V * P d x) + V ^ 2 * P d x := by
    calc
      _ = ∑ i ∈ Finset.range (d + 1),
          (weight d i x * ((i : ℝ) - d / 2) ^ 4 -
           2 * V * (weight d i x * ((i : ℝ) - d / 2) ^ 2) + V ^ 2 * weight d i x) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, ← h2, ← h4]
        rfl
  rw [heq] at hnn
  have : 0 ≤ P d x * (centralMoment d x 4 - V ^ 2) := by nlinarith
  have := (mul_nonneg_iff_of_pos_left hp).mp this
  dsimp [V] at this
  linarith

end

end Davis
