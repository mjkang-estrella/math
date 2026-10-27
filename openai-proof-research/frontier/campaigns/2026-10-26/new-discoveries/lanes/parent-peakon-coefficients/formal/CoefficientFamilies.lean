import PartitionExpansion

set_option autoImplicit false
set_option warningAsError true

namespace PeakonCoefficients

open scoped Nat

variable {K : Type*} [Field K] [CharZero K]

theorem coefficientWeight_singleton (m : ℕ) (hm : 0 < m) :
    coefficientWeight (K := K) m {m} = 1 := by
  rw [coefficientWeight_formula m {m} (by simp)]
  have hm0 : (m : K) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  simp [multiplicityDenominator, hm0]

theorem multiplicityDenominator_replicate (m : ℕ) :
    multiplicityDenominator (Multiset.replicate m 1) = m ! := by
  cases m with
  | zero => simp [multiplicityDenominator]
  | succ m =>
    unfold multiplicityDenominator
    rw [Multiset.toFinset_replicate, ite_eq_right (Nat.succ_ne_zero m),
      Finset.prod_singleton, Multiset.count_replicate_self]

theorem coefficientWeight_all_ones (m : ℕ) (hm : 0 < m) :
    coefficientWeight (K := K) m (Multiset.replicate m 1) = 1 := by
  rw [coefficientWeight_formula m _ (by simpa)]
  simp only [Multiset.card_replicate, multiplicityDenominator_replicate,
    Multiset.map_replicate, Nat.cast_one, Multiset.prod_replicate, one_pow, one_mul]
  have hf : (m : K) * ((m - 1)! : K) = (m ! : K) := by
    exact_mod_cast Nat.mul_factorial_pred (Nat.ne_of_gt hm)
  rw [hf, div_self (by exact_mod_cast Nat.factorial_ne_zero m)]

theorem multiplicityDenominator_one_big (k j : ℕ) (hk : 1 < k) :
    multiplicityDenominator (k ::ₘ Multiset.replicate j 1) = j ! := by
  cases j with
  | zero => simp [multiplicityDenominator]
  | succ j =>
    have hk1 : k ≠ 1 := by omega
    unfold multiplicityDenominator
    rw [Multiset.toFinset_cons, Multiset.toFinset_replicate,
      ite_eq_right (Nat.succ_ne_zero j), Finset.prod_insert (by simpa using hk1),
      Finset.prod_singleton, Multiset.count_cons_self,
      Multiset.count_cons_of_ne (Ne.symm hk1)]
    simp [Multiset.count_replicate, hk1, Ne.symm hk1]

theorem coefficientWeight_one_big (m j : ℕ) (hj : j < m - 1) :
    coefficientWeight (K := K) m ((m - j) ::ₘ Multiset.replicate j 1) =
      (m : K) / (m - j : ℕ) := by
  have hk : 1 < m - j := by omega
  rw [coefficientWeight_formula m _ (by simp), multiplicityDenominator_one_big _ _ hk]
  simp only [Multiset.card_cons, Multiset.card_replicate, Nat.add_sub_cancel,
    Multiset.map_cons, Multiset.prod_cons, Multiset.map_replicate, Nat.cast_one,
    Multiset.prod_replicate, one_pow, mul_one]
  have hj0 : (j ! : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  field_simp

end PeakonCoefficients
