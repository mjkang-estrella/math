import HamiltonianSupport

set_option autoImplicit false
set_option warningAsError true

namespace PeakonCoefficients

open Matrix PowerSeries

variable {K : Type*} [Field K] [CharZero K]
variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

theorem trace_all_orders_universal (u v : n → K) (lam xi gamma : K)
    (hcurve : xi ^ 2 = lam ^ 2 + gamma * lam + 1) (m : ℕ) (hm : 0 < m) :
    Matrix.trace (algebraicLax u v lam xi ^ m) =
      ∑ j ∈ Finset.range m, (m : K) / (j + 1 : K) * lam ^ (j + 1) *
        coeff m (finiteHamiltonianSeries (Finset.Icc 1 m) (rawHamiltonian u v gamma) ^ (j + 1)) := by
  rw [trace_all_orders u v lam xi gamma hcurve m hm, hamiltonianPolynomial_as_finiteSeries]
  apply Finset.sum_congr rfl
  intro j hj
  rw [finiteHamiltonianSeries_card_to_order]

theorem trace_partition_universal (u v : n → K) (lam xi gamma : K)
    (hcurve : xi ^ 2 = lam ^ 2 + gamma * lam + 1) (m : ℕ) (hm : 0 < m) :
    Matrix.trace (algebraicLax u v lam xi ^ m) =
      ∑ j ∈ Finset.range m, ∑ p ∈ (Finset.Icc 1 m).sym (j + 1),
        if p.val.sum = m then coefficientWeight (K := K) m p.val * lam ^ (j + 1) *
          (p.val.map (rawHamiltonian u v gamma)).prod else 0 := by
  rw [trace_all_orders_universal u v lam xi gamma hcurve m hm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [finiteHamiltonianSeries_power, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Multiset.map_id]
  by_cases hpm : p.val.sum = m
  · rw [ite_eq_left hpm, ite_eq_left hpm, Multiset.prod_map_div]
    unfold coefficientWeight
    rw [show p.val.card = j + 1 from p.property]
    push_cast
    ring
  · rw [ite_eq_right hpm, ite_eq_right hpm, mul_zero]

end PeakonCoefficients
