import LiteralHankel

set_option autoImplicit false
set_option warningAsError true
set_option linter.unnecessarySeqFocus false

noncomputable section
namespace JacobiShifted.SourceBridge

@[simp] theorem inverseFactor_succ_zero (s : ℕ) : inverseFactorCoeff (s+1) 0=0 := by
  simp [inverseFactorCoeff]

theorem inverseFactor_shift (s n : ℕ) : inverseFactorCoeff (s+1) (n+1)=
    ∑ k ∈ Finset.range (n+1), ((s+1 : ℕ) : ℚ)^k*inverseFactorCoeff s (n-k) := by
  rw [inverseFactorCoeff, Finset.sum_range_succ']
  simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, Nat.add_sub_add_right,
    ite_true, add_zero]

theorem inverseFactor_recurrence (s n : ℕ) :
    inverseFactorCoeff (s+1) (n+1)=
      inverseFactorCoeff s n+((s+1 : ℕ) : ℚ)*inverseFactorCoeff (s+1) n := by
  cases n with
  | zero => simp [inverseFactor_shift]
  | succ n =>
    rw [inverseFactor_shift, Finset.sum_range_succ', inverseFactor_shift, Finset.mul_sum]
    simp only [pow_zero, one_mul, Nat.sub_zero, Nat.add_sub_add_right]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_succ]
    ring

theorem inverseFactor_vanish (s n : ℕ) (hn : n<s) : inverseFactorCoeff s n=0 := by
  induction s generalizing n with
  | zero => omega
  | succ s ih =>
    cases n with
    | zero => exact inverseFactor_succ_zero s
    | succ n =>
      rw [inverseFactor_shift]
      apply Finset.sum_eq_zero
      intro k _
      rw [ih (n-k) (by omega), mul_zero]

def weight (s n : ℕ) : G := coeffEmbed (MvPolynomial.C (inverseFactorCoeff s n))

theorem weight_recurrence (s n : ℕ) :
    weight (s+1) (n+1)=weight s n+((s+1 : ℕ) : G)*weight (s+1) n := by
  simp only [weight, inverseFactor_recurrence, map_add, map_mul, map_natCast]

@[simp] theorem weight_succ_zero (s : ℕ) : weight (s+1) 0=0 := by
  simp [weight]

theorem weight_vanish (s n : ℕ) (hn : n<s) : weight s n=0 := by
  simp [weight, inverseFactor_vanish s n hn]

@[simp] theorem deltaG_weight (s n : ℕ) : deltaG (weight s n)=0 :=
  deltaG_coeffEmbed _

theorem F_weighted (n : ℕ) : F n=∑ s ∈ Finset.range (n+1), weight s n*C s := rfl

@[simp] theorem C_zero : C 0=1 := by
  simp [C_divided, a, hankelDivided, hankelNumerator]

@[simp] theorem deltaG_C_zero : deltaG (C 0)=0 := by simp

theorem deltaG_F (n : ℕ) :
    deltaG (F n)=∑ s ∈ Finset.range (n+1), weight s n*deltaG (C s) := by
  simp only [F_weighted, map_sum, deltaG_mul, deltaG_weight, zero_mul, zero_add]

theorem deltaG_F_next (n : ℕ) :
    deltaG (F (n+1))=
      (∑ s ∈ Finset.range (n+1), weight s n*deltaG (C (s+1)))+
      ∑ s ∈ Finset.range (n+1), (s : G)*weight s n*deltaG (C s) := by
  rw [deltaG_F, Finset.sum_range_succ']
  simp only [deltaG_C_zero, mul_zero, add_zero, weight_recurrence, add_mul,
    Finset.sum_add_distrib]
  apply congrArg (fun z : G => (∑ s ∈ Finset.range (n+1), weight s n*deltaG (C (s+1)))+z)
  rw [Finset.sum_range_succ]
  simp only [weight_vanish (n+1) n (by omega), mul_zero, zero_mul, add_zero]
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero]

/-- Exact inverse-factorial conversion of the finite Hankel identity. -/
theorem literal_F_R2 (n : ℕ) :
    deltaG (deltaG (F n))+imaginaryUnit*deltaG (F (n+1))-potentialCurve*F n=0 := by
  rw [deltaG_F, map_sum, deltaG_F_next, F_weighted]
  simp only [deltaG_mul, deltaG_weight, zero_mul, zero_add, mul_add, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ s ∈ Finset.range (n+1), weight s n*
      (deltaG (deltaG (C s))+imaginaryUnit*(s : G)*deltaG (C s)+
        imaginaryUnit*deltaG (C (s+1))-potentialCurve*C s) := by
          apply Finset.sum_congr rfl
          intro s _
          ring
    _ = 0 := by simp only [literal_hankel_R1, mul_zero, Finset.sum_const_zero]

end JacobiShifted.SourceBridge
