import ArrowheadGrid

open Finset Filter
open scoped Topology
namespace FlatBernoulli
noncomputable section

def gridPowerMean (N k : ℕ) : ℝ := (∑ i : Fin N, gridNode N i^k)/(N:ℝ)

theorem gridPowerMean_expansion (N k : ℕ) (hN : 0 < N) :
    gridPowerMean N k = ∑ i ∈ Finset.range (k+1),
      ((bernoulli i:ℝ)*((k+1).choose i:ℝ)/(k+1)) * ((N:ℝ)⁻¹)^i := by
  have hNne : (N:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hF : (∑ j ∈ Finset.range N, (j:ℝ)^k) =
      ∑ i ∈ Finset.range (k+1),
        (bernoulli i:ℝ)*((k+1).choose i:ℝ)*(N:ℝ)^(k+1-i)/(k+1) := by
    exact_mod_cast sum_range_pow N k
  have hnorm : gridPowerMean N k =
      (∑ j ∈ Finset.range N, (j:ℝ)^k)/(N:ℝ)^(k+1) := by
    simp only [gridPowerMean, gridNode, div_pow, ← Finset.sum_div]
    rw [Fin.sum_univ_eq_sum_range (fun j => (j:ℝ)^k) N, div_div, pow_succ]
  rw [hnorm,hF,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hile : i ≤ k+1 := by have := Finset.mem_range.mp hi; omega
  have hcancel : (N:ℝ)^(k+1-i)/(N:ℝ)^(k+1) = ((N:ℝ)⁻¹)^i := by
    rw [pow_sub₀ (N:ℝ) hNne hile]
    field_simp
    rw [one_div, inv_pow, mul_inv_cancel₀ (pow_ne_zero i hNne)]
  calc
    _ = ((bernoulli i:ℝ)*((k+1).choose i:ℝ)/(k+1))*
        ((N:ℝ)^(k+1-i)/(N:ℝ)^(k+1)) := by ring
    _ = _ := by rw [hcancel]

theorem gridPowerMean_tendsto (k : ℕ) :
    Tendsto (fun N : ℕ => gridPowerMean N k) atTop (𝓝 ((k+1:ℝ)⁻¹)) := by
  have hinv : Tendsto (fun N : ℕ => (N:ℝ)⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hs : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range (k+1),
      ((bernoulli i:ℝ)*((k+1).choose i:ℝ)/(k+1))*((N:ℝ)⁻¹)^i)
      atTop (𝓝 (∑ i ∈ Finset.range (k+1),
      ((bernoulli i:ℝ)*((k+1).choose i:ℝ)/(k+1))*(0:ℝ)^i)) :=
    tendsto_finsetSum (Finset.range (k+1)) (fun i _ =>
      tendsto_const_nhds.mul (hinv.pow i))
  have heq : (∑ i ∈ Finset.range (k+1),
      ((bernoulli i:ℝ)*((k+1).choose i:ℝ)/(k+1)) * (0:ℝ)^i) = (k+1:ℝ)⁻¹ := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro i _ hi
      simp [zero_pow hi]
    · simp
  rw [heq] at hs
  apply hs.congr'
  filter_upwards [Filter.eventually_atTop.2 ⟨1,fun N hN => hN⟩] with N hN
  exact (gridPowerMean_expansion N k (by omega)).symm

end
end FlatBernoulli
