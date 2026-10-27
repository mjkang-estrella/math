import WeightedPowers

open Finset
namespace FlatBernoulli
variable {ι : Type*} [Fintype ι]

theorem even_propagation (w z : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hz : ∀ i, 0 ≤ z i) {q T c : ℝ} (hq0 : 1/2 ≤ q) (hq1 : q ≤ 1)
    (hc : 0 < c) (hbase : T-(∑ i, w i) ≤ -c)
    (hnext : q^2*(T-(∑ i, w i*z i)) ≤ T-(∑ i, w i)) (m : ℕ) :
    q^(2*m)*(T-(∑ i, w i*z i^m)) ≤ -c*(1/4)^m := by
  have hq : 0 < q := by linarith
  have hq2 : 0 < q^2 := sq_pos_of_pos hq
  have hsq1 : q^2 ≤ 1 := by nlinarith
  have hp : 0 ≤ (q^2-1)*(T-(∑ i, w i)) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  have hmul : 0 ≤ q^2*((∑ i, w i*z i)-(∑ i, w i)) := by nlinarith
  have hmean : (∑ i, w i) ≤ ∑ i, w i*z i := by
    by_contra hn
    have hh : q^2*((∑ i, w i*z i)-(∑ i, w i)) < 0 :=
      mul_neg_of_pos_of_neg hq2 (by linarith)
    linarith
  have hpower := weighted_power_ge_mass w z hw hz hmean m
  have hsq0 : (1/4:ℝ) ≤ q^2 := by nlinarith
  have hbound : (1/4:ℝ)^m ≤ q^(2*m) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by norm_num) hsq0 m
  calc
    q^(2*m)*(T-(∑ i, w i*z i^m)) ≤ q^(2*m)*(T-(∑ i, w i)) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left hpower T) (pow_nonneg hq.le _)
    _ ≤ q^(2*m)*(-c) := mul_le_mul_of_nonneg_left hbase (pow_nonneg hq.le _)
    _ ≤ -c*(1/4)^m := by nlinarith

end FlatBernoulli
