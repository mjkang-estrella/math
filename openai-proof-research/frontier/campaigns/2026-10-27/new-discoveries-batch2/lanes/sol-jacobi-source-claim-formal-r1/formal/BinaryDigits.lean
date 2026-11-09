import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option warningAsError true

namespace JacobiShifted.BinaryFiltration

def sigma (n : ℕ) : ℕ := (Nat.digits 2 n).sum

@[simp] theorem sigma_zero : sigma 0 = 0 := by simp [sigma]

@[simp] theorem sigma_one : sigma 1 = 1 := by
  simp [sigma]

theorem sigma_pos {n : ℕ} (hn : n ≠ 0) : 0 < sigma n := by
  have hnil : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  exact List.sum_pos_iff_exists_pos_nat.mpr
    ⟨_, List.getLast_mem hnil, Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero 2 hn)⟩

@[simp] theorem sigma_double (n : ℕ) : sigma (2 * n) = sigma n := by
  by_cases hn : n = 0
  · simp [hn]
  · simp [sigma, Nat.digits_base_mul (by omega : 1 < 2) (Nat.pos_of_ne_zero hn)]

theorem sigma_odd (n : ℕ) : sigma (2 * n + 1) = sigma n + 1 := by
  have h := Nat.digits_add 2 (by omega) 1 n (by omega) (Or.inl (by omega))
  simpa [sigma, Nat.add_comm, List.sum_cons] using congrArg List.sum h

theorem sigma_odd_pred {j : ℕ} (hj : Odd j) : sigma j = sigma (j - 1) + 1 := by
  obtain ⟨k, rfl⟩ := hj
  rw [Nat.add_sub_cancel, sigma_double]
  exact sigma_odd k

/-- Use the exact factorial product identity and Legendre with bounded subtractions.
No inequality is inferred from a truncated Kummer subtraction. -/
theorem sigma_add_le (n k : ℕ) : sigma (n + k) ≤ sigma n + sigma k := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hprod := congrArg (padicValNat 2) (Nat.add_choose_mul_factorial_mul_factorial n k)
  rw [padicValNat.mul (Nat.mul_ne_zero
    (Nat.choose_ne_zero (Nat.le_add_left k n)) (Nat.factorial_ne_zero n))
    (Nat.factorial_ne_zero k),
    padicValNat.mul (Nat.choose_ne_zero (Nat.le_add_left k n))
      (Nat.factorial_ne_zero n)] at hprod
  have hn := sub_one_mul_padicValNat_factorial (p := 2) n
  have hk := sub_one_mul_padicValNat_factorial (p := 2) k
  have hnk := sub_one_mul_padicValNat_factorial (p := 2) (n + k)
  have bn := Nat.digit_sum_le 2 n
  have bk := Nat.digit_sum_le 2 k
  have bnk := Nat.digit_sum_le 2 (n + k)
  simp only [show 2 - 1 = 1 from rfl, one_mul] at hn hk hnk
  change padicValNat 2 n.factorial = n - sigma n at hn
  change padicValNat 2 k.factorial = k - sigma k at hk
  change padicValNat 2 (n + k).factorial = n + k - sigma (n + k) at hnk
  change sigma n ≤ n at bn
  change sigma k ≤ k at bk
  change sigma (n + k) ≤ n + k at bnk
  omega

end JacobiShifted.BinaryFiltration
