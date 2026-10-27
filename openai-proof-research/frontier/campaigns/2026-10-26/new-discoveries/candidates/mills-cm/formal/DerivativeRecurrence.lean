import Mills

open scoped BigOperators Topology
open Filter

namespace MillsCounterexample

theorem quotient_contDiffAt_zero (n : ℕ) : ContDiffAt ℝ n quotient 0 := by
  have hr := (mills_contDiff_nat n).contDiffAt (x := 0)
  have hden : (1 : ℝ) - 0 * mills 0 ≠ 0 := by norm_num
  change ContDiffAt ℝ n (fun x => quotient x) 0
  simp_rw [quotient_eq, div_eq_mul_inv]
  exact (hr.pow 2).mul ((contDiffAt_const.sub (contDiffAt_id.mul hr)).inv hden)

theorem quotient_zero : quotient 0 = mills 0 ^ 2 := by simp [quotient_eq]

theorem quotient_identity_near_zero :
    (fun x => quotient x - x * (mills x * quotient x)) =ᶠ[𝓝 0]
      (fun x => mills x * mills x) := by
  have hc : ContinuousAt (fun x : ℝ => 1 - x * mills x) 0 :=
    continuousAt_const.sub (continuousAt_id.mul (mills_hasDerivAt 0).continuousAt)
  have hn : ∀ᶠ x in 𝓝 (0 : ℝ), 1 - x * mills x ≠ 0 :=
    hc.eventually_ne (by norm_num)
  filter_upwards [hn] with x hx
  calc
    quotient x - x * (mills x * quotient x) =
        quotient x * (1 - x * mills x) := by ring
    _ = mills x * mills x := by rw [quotient_eq, div_mul_cancel₀ _ hx, pow_two]

theorem iteratedDeriv_id_mul_zero (n : ℕ) (f : ℝ → ℝ)
    (hf : ContDiffAt ℝ n f 0) :
    iteratedDeriv n (fun x => x * f x) 0 =
      if n = 0 then 0 else (n : ℝ) * iteratedDeriv (n - 1) f 0 := by
  rw [iteratedDeriv_fun_mul (f := fun x : ℝ => x) (g := f) contDiffAt_id hf]
  simp only [iteratedDeriv_fun_id_zero, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  cases n <;> simp

theorem mills_derivative_succ_succ (n : ℕ) :
    iteratedDeriv (n + 2) mills 0 = (n + 1 : ℕ) * iteratedDeriv n mills 0 := by
  have hr := (mills_contDiff_nat (n + 1)).contDiffAt (x := 0)
  have hmul := (contDiffAt_id.mul hr)
  have hh := iteratedDeriv_fun_sub (n := n + 1) hmul
    (contDiffAt_const (c := (1 : ℝ)))
  simp only [id_eq] at hh
  rw [show n + 2 = (n + 1) + 1 by omega, iteratedDeriv_succ', mills_deriv]
  rw [hh, iteratedDeriv_id_mul_zero (n + 1) mills hr]
  simp [iteratedDeriv_const]

theorem quotient_derivative_recurrence (n : ℕ) :
    iteratedDeriv (n + 1) quotient 0 =
      (∑ k ∈ Finset.range (n + 2), ((n + 1).choose k : ℝ) *
        iteratedDeriv k mills 0 * iteratedDeriv (n + 1 - k) mills 0) +
      (n + 1 : ℕ) * (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
        iteratedDeriv k mills 0 * iteratedDeriv (n - k) quotient 0) := by
  have hr := (mills_contDiff_nat (n + 1)).contDiffAt (x := 0)
  have hf := quotient_contDiffAt_zero (n + 1)
  have he := quotient_identity_near_zero.iteratedDeriv_eq (n + 1)
  have hh := iteratedDeriv_fun_sub (n := n + 1) hf (contDiffAt_id.mul (hr.mul hf))
  simp only [id_eq] at hh
  rw [hh,
    iteratedDeriv_id_mul_zero (n + 1) (fun x => mills x * quotient x) (hr.mul hf)] at he
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
    Nat.add_sub_cancel] at he
  rw [iteratedDeriv_fun_mul hr hr,
    iteratedDeriv_fun_mul (hr.of_le (by exact_mod_cast Nat.le_succ n))
      (hf.of_le (by exact_mod_cast Nat.le_succ n))] at he
  linarith

end MillsCounterexample
