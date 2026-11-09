module
public import BesselInterfaces
public section
noncomputable section
open scoped Topology
open Filter
namespace BesselRatio

theorem scalarSeries_deriv {f : ℝ → ℝ} {c : ℕ → ℝ}
    (h : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℝ c) 0 ⊤) :
    HasFPowerSeriesOnBall (deriv f)
      (FormalMultilinearSeries.ofScalars ℝ (fun n => (n+1:ℝ)*c (n+1))) 0 ⊤ := by
  have hd := (ContinuousLinearMap.apply ℝ ℝ (1:ℝ)).comp_hasFPowerSeriesOnBall h.fderiv
  have he : (ContinuousLinearMap.apply ℝ ℝ (1:ℝ)).compFormalMultilinearSeries
      (FormalMultilinearSeries.ofScalars ℝ c).derivSeries =
      FormalMultilinearSeries.ofScalars ℝ (fun n => (n+1:ℝ)*c (n+1)) := by
    apply FormalMultilinearSeries.ext
    intro n
    apply ContinuousMultilinearMap.ext_ring
    change ((FormalMultilinearSeries.ofScalars ℝ c).derivSeries.coeff n) 1 = _
    rw [FormalMultilinearSeries.derivSeries_coeff_one, FormalMultilinearSeries.coeff_ofScalars]
    simp [FormalMultilinearSeries.ofScalars, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  rw [he] at hd
  exact hd

@[expose] def dc (ν : ℝ) (n : ℕ) : ℝ := (n+1)*coeff ν (n+1)
@[expose] def ddc (ν : ℝ) (n : ℕ) : ℝ := (n+1)*dc ν (n+1)

theorem S_deriv_series {ν : ℝ} (hν : -1 < ν) :
    HasFPowerSeriesOnBall (deriv (S ν)) (FormalMultilinearSeries.ofScalars ℝ (dc ν)) 0 ⊤ :=
  scalarSeries_deriv (S_hasFPowerSeries hν)

theorem S_second_series {ν : ℝ} (hν : -1 < ν) :
    HasFPowerSeriesOnBall (deriv (deriv (S ν))) (FormalMultilinearSeries.ofScalars ℝ (ddc ν)) 0 ⊤ :=
  scalarSeries_deriv (S_deriv_series hν)

theorem S_ode {ν t : ℝ} (hν : -1 < ν) :
    4*t*deriv (deriv (S ν)) t + 4*(ν+1)*deriv (S ν) t = S ν t := by
  have hd : HasSum (fun n => dc ν n * t^n) (deriv (S ν) t) := by
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using
      (S_deriv_series hν).hasSum (y := t) (by simp)
  have hdd : HasSum (fun n => ddc ν n * t^n) (deriv (deriv (S ν)) t) := by
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using
      (S_second_series hν).hasSum (y := t) (by simp)
  have hshift : HasSum (fun n : ℕ => 4*n*dc ν n*t^n) (4*t*deriv (deriv (S ν)) t) := by
    apply (hasSum_nat_add_iff' 1).mp
    simp only [Finset.sum_range_one, Nat.cast_zero, mul_zero, zero_mul, sub_zero]
    convert hdd.mul_left (4*t) using 1
    funext n
    dsimp [ddc]
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    ring
  have hh := hshift.add (hd.mul_left (4*(ν+1)))
  have he : (fun n : ℕ => 4*n*dc ν n*t^n + 4*(ν+1)*(dc ν n*t^n)) =
      (fun n => coeff ν n*t^n) := by
    funext n
    have hp : (n:ℝ)+ν+1 ≠ 0 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hn : (n:ℝ)+1 ≠ 0 := by positivity
    dsimp [dc]
    rw [coeff_succ hν]
    field_simp
    ring
  rw [he] at hh
  exact hh.unique (summable_S hν).hasSum
end BesselRatio
