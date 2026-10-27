import GridPowerLimits
import ArrowheadRecurrence

open Finset Filter
open scoped Topology
namespace FlatBernoulli
noncomputable section

def gridKernel (N k : ℕ) : ℝ := ∑ i : Fin N, gridV N i^2*gridNode N i^k

theorem gridKernel_eq_power_difference (N k : ℕ) (hN : 0 < N) :
    gridKernel N k = gridPowerMean N k-gridPowerMean N (k+1) := by
  unfold gridKernel
  simp_rw [gridV,mul_pow,gridS_sq N hN,gridR_sq]
  have he : ∀ i : Fin N, (1-gridNode N i)*(N:ℝ)⁻¹*gridNode N i^k =
      (gridNode N i^k-gridNode N i^(k+1))/(N:ℝ) := by
    intro i
    rw [pow_succ]
    ring
  simp_rw [he]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, sub_div]
  rfl

theorem gridKernel_tendsto (k : ℕ) :
    Tendsto (fun N : ℕ => gridKernel N k) atTop
      (𝓝 (1/(((k:ℝ)+2)*((k:ℝ)+1)))) := by
  have h := (gridPowerMean_tendsto k).sub (gridPowerMean_tendsto (k+1))
  have he : ((k+1:ℝ)⁻¹)-((k+1+1:ℝ)⁻¹) = 1/(((k:ℝ)+2)*((k:ℝ)+1)) := by
    have h1 : (k:ℝ)+1 ≠ 0 := by positivity
    have h2 : (k:ℝ)+2 ≠ 0 := by positivity
    rw [show (k:ℝ)+1+1 = (k:ℝ)+2 by ring]
    field_simp
    ring
  norm_num only [Nat.cast_add, Nat.cast_one] at h
  rw [he] at h
  apply h.congr'
  filter_upwards [Filter.eventually_atTop.2 ⟨1,fun N hN => hN⟩] with N hN
  exact (gridKernel_eq_power_difference N k (by omega)).symm

/-- The normalized coefficients of the source generating function. The finite
composition bridge is supplied separately; it is not an assumption here. -/
def renewalCoefficient : ℕ → ℝ
  | 0 => 1
  | 1 => 0
  | n+2 => ∑ k ∈ Finset.range (n+1),
      (1/(((k:ℝ)+2)*((k:ℝ)+1)))*renewalCoefficient (n-k)
termination_by n => n

def gridMoment (N n : ℕ) : ℝ := centerMoment (gridNode N) (gridV N) n

theorem gridMoment_tendsto (n : ℕ) :
    Tendsto (fun N : ℕ => gridMoment N n) atTop (𝓝 (renewalCoefficient n)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | (_ | n)
    · simpa only [gridMoment,centerMoment_zero,renewalCoefficient] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1))
    · simpa only [Nat.zero_add,gridMoment,centerMoment_one,renewalCoefficient] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
    · rw [renewalCoefficient]
      have ht : ∀ k ∈ Finset.range (n+1),
          Tendsto (fun N : ℕ => gridKernel N k * gridMoment N (n-k)) atTop
            (𝓝 ((1/(((k:ℝ)+2)*((k:ℝ)+1)))*renewalCoefficient (n-k))) := by
        intro k _
        exact (gridKernel_tendsto k).mul (ih (n-k) (by omega))
      have h := tendsto_finsetSum (Finset.range (n+1)) ht
      apply h.congr'
      exact Filter.Eventually.of_forall fun N => (centerMoment_convolution
        (gridNode N) (gridV N) n).symm

end
end FlatBernoulli
