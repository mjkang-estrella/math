import TrigCertificate

namespace TrigCertificate

lemma B_zero : B 0=1 := by decide
lemma C_zero : C 0=1 := by decide
lemma C_one : C 1=523 := by decide

lemma B_recurrence (k : ℕ) (hk : 0<k) (hN : k≤949) :
    2*(k:ℤ)*B k = 4*(2*(k:ℤ)-1)*B (k-1) +
      (if 50≤k then (4:ℤ)^50*(2*(k:ℤ)-150)*B (k-50) else 0) -
      (if 51≤k then (4:ℤ)^51*(2*(k:ℤ)-151)*B (k-51) else 0) := by
  have h := List.all_eq_true.mp bRecCheck_ok k (List.mem_range.mpr (by omega))
  have hk' : k≠0 := by omega
  simp only [hk', ite_false] at h
  exact of_decide_eq_true h

lemma C_recurrence (k : ℕ) (hk : 2≤k) (hN : k≤949) :
    C k=1046*C (k-1)-277729*C (k-2) := by
  have h := List.all_eq_true.mp cRecCheck_ok k (List.mem_range.mpr (by omega))
  have hk0 : k≠0 := by omega
  have hk1 : k≠1 := by omega
  simp only [hk0, hk1, ite_false] at h
  exact of_decide_eq_true h

def certCoeff (k : ℕ) : ℚ := (B k:ℚ)/(4:ℚ)^k

lemma certCoeff_zero : certCoeff 0=1 := by simp [certCoeff, B_zero]

lemma scale_certCoeff (k j : ℕ) (hj : j≤k) :
    (4:ℚ)^k*certCoeff (k-j)=(4:ℚ)^j*(B (k-j):ℚ) := by
  unfold certCoeff
  have hp : (4:ℚ)^k=(4:ℚ)^j*(4:ℚ)^(k-j) := by
    rw [← pow_add, Nat.add_sub_of_le hj]
  rw [hp]
  field_simp

lemma certCoeff_recurrence (k : ℕ) (hk : 0<k) (hN : k≤949) :
    (2*(k:ℚ))*certCoeff k = (2*(k:ℚ)-1)*certCoeff (k-1) +
      (if 50≤k then (2*(k:ℚ)-150)*certCoeff (k-50) else 0) -
      (if 51≤k then (2*(k:ℚ)-151)*certCoeff (k-51) else 0) := by
  have h := B_recurrence k hk hN
  have hq : (2*(k:ℚ))*(B k:ℚ) = 4*(2*(k:ℚ)-1)*(B (k-1):ℚ) +
      (if 50≤k then (4:ℚ)^50*(2*(k:ℚ)-150)*(B (k-50):ℚ) else 0) -
      (if 51≤k then (4:ℚ)^51*(2*(k:ℚ)-151)*(B (k-51):ℚ) else 0) := by
    exact_mod_cast h
  apply mul_left_cancel₀ (pow_ne_zero k (show (4:ℚ)≠0 by norm_num))
  have h0 := scale_certCoeff k 0 (Nat.zero_le k)
  simp only [Nat.sub_zero, pow_zero, one_mul] at h0
  have h1 := scale_certCoeff k 1 hk
  simp only [pow_one] at h1
  by_cases h50 : 50≤k <;> by_cases h51 : 51≤k
  · have h50' := scale_certCoeff k 50 h50
    have h51' := scale_certCoeff k 51 h51
    simp only [h50, h51, ite_true] at hq ⊢
    linear_combination hq + (2*(k:ℚ))*h0 - (2*(k:ℚ)-1)*h1 -
      (2*(k:ℚ)-150)*h50' + (2*(k:ℚ)-151)*h51'
  · have h50' := scale_certCoeff k 50 h50
    simp only [h50, h51, ite_true, ite_false] at hq ⊢
    linear_combination hq + (2*(k:ℚ))*h0 - (2*(k:ℚ)-1)*h1 - (2*(k:ℚ)-150)*h50'
  · omega
  · simp only [h50, h51, ite_false] at hq ⊢
    linear_combination hq + (2*(k:ℚ))*h0 - (2*(k:ℚ)-1)*h1

def hornerPrefix (n : ℕ) : ℤ :=
  (List.range n).foldl (fun h k => 2108*h+B k*C k) 0

lemma hornerPrefix_succ (n : ℕ) :
    hornerPrefix (n+1)=2108*hornerPrefix n+B n*C n := by
  simp [hornerPrefix, List.range_succ, List.foldl_append]

lemma hornerPrefix_eq_sum (n : ℕ) :
    hornerPrefix n=∑ k∈Finset.range n,B k*C k*(2108:ℤ)^(n-1-k) := by
  induction n with
  | zero => simp [hornerPrefix]
  | succ n ih =>
    rw [hornerPrefix_succ, ih, Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
    have hs : (2108:ℤ)*(∑ k∈Finset.range n,B k*C k*(2108:ℤ)^(n-1-k)) =
        ∑ k∈Finset.range n,B k*C k*(2108:ℤ)^(n-k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hkn := Finset.mem_range.mp hk
      have he : n-k=(n-1-k)+1 := by omega
      rw [he, pow_succ]
      ring
    rw [hs]

lemma numerator_neg : (∑ k∈Finset.range 950,B k*C k*(2108:ℤ)^(949-k))<0 := by
  rw [← hornerPrefix_eq_sum]
  exact hornerValue_neg

end TrigCertificate
