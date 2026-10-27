import TraceExpansion

set_option autoImplicit false
set_option warningAsError true

namespace PeakonCoefficients

open PowerSeries
open scoped Nat

variable {K : Type*} [Field K]

noncomputable def finiteHamiltonianSeries (s : Finset ℕ) (h : ℕ → K) : PowerSeries K :=
  ∑ k ∈ s, monomial k (h k / (k : K))

theorem multiset_prod_monomials (p : Multiset ℕ) (d : ℕ → ℕ) (a : ℕ → K) :
    (p.map (fun k => monomial (d k) (a k))).prod =
      monomial (p.map d).sum (p.map a).prod := by
  induction p using Multiset.induction_on with
  | empty => simp [monomial_zero_eq_C_apply]
  | @cons k p ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, ih]
    rw [monomial_mul_monomial]

theorem finiteHamiltonianSeries_power (s : Finset ℕ) (h : ℕ → K) (j m : ℕ) :
    coeff m (finiteHamiltonianSeries s h ^ j) =
      ∑ p ∈ s.sym j,
        if (p.val.map id).sum = m then
          (p.val.countPerms : K) * (p.val.map (fun k => h k / (k : K))).prod else 0 := by
  rw [finiteHamiltonianSeries, Finset.sum_pow, map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [coeff_natCast_mul, multiset_prod_monomials, coeff_monomial]
  by_cases hpm : (p.val.map id).sum = m
  · simp [id_eq] at hpm
    simp [hpm]
  · simp [id_eq] at hpm
    simp [hpm, Ne.symm hpm]



theorem multiplicity_factorial_countPerms (p : Multiset ℕ) :
    (∏ k ∈ p.toFinset, (p.count k)!) * p.countPerms = p.card ! := by
  have hs := Nat.multinomial_spec p.toFinsupp.support p.toFinsupp
  have hsum : (∑ k ∈ p.toFinsupp.support, p.toFinsupp k) = p.card :=
    p.toFinsupp_sum_eq
  rw [hsum] at hs
  simpa only [Multiset.countPerms, Finsupp.multinomial_eq,
    Multiset.toFinsupp_support, Multiset.toFinsupp_apply] using hs



def multiplicityDenominator (p : Multiset ℕ) : ℕ :=
  ∏ k ∈ p.toFinset, (p.count k)!

noncomputable def coefficientWeight (m : ℕ) (p : Multiset ℕ) : K :=
  (m : K) / (p.card : K) * (p.countPerms : K) / (p.map (fun k : ℕ => (k : K))).prod

section CharZero
variable [CharZero K]

theorem coefficientWeight_formula (m : ℕ) (p : Multiset ℕ) (hp : 0 < p.card) :
    coefficientWeight (K := K) m p =
      (m : K) * ((p.card - 1)! : K) /
        ((p.map (fun k : ℕ => (k : K))).prod * (multiplicityDenominator p : K)) := by
  have hdpos : 0 < multiplicityDenominator p :=
    Finset.prod_pos (fun k hk => Nat.factorial_pos (p.count k))
  have hd0 : (multiplicityDenominator p : K) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hdpos
  have hc0 : (p.card : K) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hp
  have hspec : (multiplicityDenominator p : K) * (p.countPerms : K) = (p.card ! : K) := by
    exact_mod_cast multiplicity_factorial_countPerms p
  have hfac : (p.card ! : K) = (p.card : K) * ((p.card - 1)! : K) := by
    exact_mod_cast (Nat.mul_factorial_pred (Nat.ne_of_gt hp)).symm
  rw [hfac] at hspec
  have hratio : (p.countPerms : K) / (p.card : K) =
      ((p.card - 1)! : K) / (multiplicityDenominator p : K) := by
    apply (div_eq_div_iff hc0 hd0).mpr
    calc
      _ = (multiplicityDenominator p : K) * (p.countPerms : K) := by ring
      _ = (p.card : K) * ((p.card - 1)! : K) := hspec
      _ = _ := by ring
  unfold coefficientWeight
  calc
    _ = (m : K) * ((p.countPerms : K) / (p.card : K)) /
        (p.map (fun k : ℕ => (k : K))).prod := by ring
    _ = _ := by rw [hratio]; ring
variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

theorem hamiltonianPolynomial_as_finiteSeries (u v : n → K) (gamma : K) :
    (hamiltonianPolynomial u v gamma : PowerSeries K) =
      finiteHamiltonianSeries (Finset.Icc 1 (Fintype.card n)) (rawHamiltonian u v gamma) := by
  change (Polynomial.coeToPowerSeries.ringHom (R := K))
    (∑ i ∈ Finset.range (Fintype.card n),
      Polynomial.C (Matrix.trace (hamiltonianDirection u v gamma * upperKernel u v ^ i)) *
      Polynomial.X ^ (i + 1)) = _
  rw [map_sum]
  unfold finiteHamiltonianSeries
  apply Finset.sum_bij (fun i _ => i + 1)
  · intro i hi
    simp only [Finset.mem_range] at hi
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro a ha b hb hab
    omega
  · intro k hk
    have hk' := Finset.mem_Icc.mp hk
    exact ⟨k - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro i hi
    rw [Polynomial.C_mul_X_pow_eq_monomial]
    change ((Polynomial.monomial (i + 1) _ : Polynomial K) : PowerSeries K) = _
    rw [Polynomial.coe_monomial]
    push_cast
    rw [rawHamiltonian_normalization]


theorem trace_partition_weights (u v : n → K) (lam xi gamma : K)
    (hcurve : xi ^ 2 = lam ^ 2 + gamma * lam + 1) (m : ℕ) (hm : 0 < m) :
    Matrix.trace (algebraicLax u v lam xi ^ m) =
      ∑ j ∈ Finset.range m, ∑ p ∈ (Finset.Icc 1 (Fintype.card n)).sym (j + 1),
        if p.val.sum = m then coefficientWeight (K := K) m p.val * lam ^ (j + 1) *
          (p.val.map (rawHamiltonian u v gamma)).prod else 0 := by
  rw [trace_all_orders u v lam xi gamma hcurve m hm, hamiltonianPolynomial_as_finiteSeries]
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

theorem trace_partition_formula (u v : n → K) (lam xi gamma : K)
    (hcurve : xi ^ 2 = lam ^ 2 + gamma * lam + 1) (m : ℕ) (hm : 0 < m) :
    Matrix.trace (algebraicLax u v lam xi ^ m) =
      ∑ j ∈ Finset.range m, ∑ p ∈ (Finset.Icc 1 (Fintype.card n)).sym (j + 1),
        if p.val.sum = m then
          ((m : K) * (j ! : K) /
            ((p.val.map (fun k : ℕ => (k : K))).prod *
              (multiplicityDenominator p.val : K))) * lam ^ (j + 1) *
            (p.val.map (rawHamiltonian u v gamma)).prod else 0 := by
  rw [trace_partition_weights u v lam xi gamma hcurve m hm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro p hp
  have hpc : p.val.card = j + 1 := p.property
  have hpos : 0 < p.val.card := by omega
  rw [coefficientWeight_formula m p.val hpos, hpc, Nat.add_sub_cancel]
end CharZero

end PeakonCoefficients
