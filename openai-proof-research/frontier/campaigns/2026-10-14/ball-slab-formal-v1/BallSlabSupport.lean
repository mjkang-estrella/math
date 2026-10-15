import Mathlib

/-!
Real scalar support for the ball-slab manuscript. These results do not
formalize inverse kernels, curve traces, regularity, asymptotics, or the
geometric theorem. The coefficient omits the common factor 1/(4*pi).
-/
namespace BallSlabSupport

noncomputable def kernelCoefficient (x : ℝ) : ℝ :=
  2 * (2 * x + 1) / (x * (x + 1) * (x * (x + 1) - 2))

theorem kernelCoefficient_telescope (x : ℝ) (hx : 1 < x) :
    kernelCoefficient x =
      1 / (x - 1) - 1 / x - 1 / (x + 1) + 1 / (x + 2) := by
  have h0 : x ≠ 0 := ne_of_gt (by linarith)
  have hm : x - 1 ≠ 0 := ne_of_gt (by linarith)
  have h1 : x + 1 ≠ 0 := ne_of_gt (by linarith)
  have h2 : x + 2 ≠ 0 := ne_of_gt (by linarith)
  have hprod : x * (x + 1) - 2 ≠ 0 := by
    have : 0 < (x - 1) * (x + 2) := mul_pos (by linarith) (by linarith)
    apply ne_of_gt
    nlinarith
  unfold kernelCoefficient
  field_simp
  ring

theorem kernelCoefficient_nonneg (x : ℝ) (hx : 1 < x) :
    0 ≤ kernelCoefficient x := by
  have hp : 0 < x * (x + 1) - 2 := by
    have : 0 < (x - 1) * (x + 2) := mul_pos (by linarith) (by linarith)
    nlinarith
  unfold kernelCoefficient
  positivity

theorem kernelCoefficient_partial_sum (n : ℕ) :
    (∑ k ∈ Finset.range n, kernelCoefficient ((k : ℝ) + 2)) =
      2 / 3 - 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 3) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    rw [kernelCoefficient_telescope ((n : ℝ) + 2) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)]
    push_cast
    ring_nf

theorem kernelCoefficient_partial_sum_bounds (n : ℕ) :
    0 ≤ (∑ k ∈ Finset.range n, kernelCoefficient ((k : ℝ) + 2)) ∧
    (∑ k ∈ Finset.range n, kernelCoefficient ((k : ℝ) + 2)) ≤ 2 / 3 := by
  constructor
  · exact Finset.sum_nonneg fun k _ => kernelCoefficient_nonneg _ (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  · rw [kernelCoefficient_partial_sum]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hi : 1 / ((n : ℝ) + 3) ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    linarith

theorem reciprocal_remainder (x y : ℝ) (hx : x ≠ 0) (hxy : x + y ≠ 0) :
    1 / (x + y) - 1 / x + y / x ^ 2 = y ^ 2 / (x ^ 2 * (x + y)) := by
  field_simp
  ring

theorem tangent_energy_remainder (h : ℝ) (hh : 0 < h) :
    (h + 1 / 4) / (h + 1 / 2) ^ 2 - 1 / h =
      (-3 / 4 * h - 1 / 4) / (h * (h + 1 / 2) ^ 2) := by
  have h0 : h ≠ 0 := ne_of_gt hh
  have h1 : h + 1 / 2 ≠ 0 := by positivity
  field_simp
  ring

end BallSlabSupport
