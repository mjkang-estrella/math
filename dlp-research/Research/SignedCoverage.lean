import Std

/-! Arithmetic coverage for zero-centered signed BSGS blocks.
This is not a group algorithm, cost model, or ECDLP correctness theorem. -/
namespace Research.SignedCoverage

def stride (m : Nat) : Nat := 2 * m - 1

def blocks (q m : Nat) : Nat := (q - 1 + (m - 1)) / stride m + 1

/-- Every canonical scalar is within m-1 of one of the proposed block centers.
The two alternatives use natural arithmetic without negative scalar values. -/
theorem covers (q m d : Nat) (hq : 0 < q) (hm : 0 < m) (hd : d < q) :
    ∃ i, i < blocks q m ∧ ∃ j, j < m ∧
      (d = i * stride m + j ∨ d + j = i * stride m) := by
  let t := d + (m - 1)
  let i := t / stride m
  have hs : 0 < stride m := by dsimp [stride]; omega
  have ht : t ≤ q - 1 + (m - 1) := by dsimp [t]; omega
  have hi : i < blocks q m := by
    have hdiv : t / stride m ≤ (q - 1 + (m - 1)) / stride m :=
      Nat.div_le_div_right ht
    dsimp [i, blocks]
    omega
  have hrem : t % stride m < 2 * m - 1 := Nat.mod_lt t hs
  have heq : t % stride m + i * stride m = t := by
    simpa [i, Nat.mul_comm] using Nat.mod_add_div t (stride m)
  refine ⟨i, hi, ?_⟩
  dsimp [t] at heq hrem
  by_cases hcenter : i * stride m ≤ d
  · refine ⟨d - i * stride m, ?_, Or.inl ?_⟩ <;> omega
  · refine ⟨i * stride m - d, ?_, Or.inr ?_⟩ <;> omega

/-- Under the proposed table-span restriction, two baby magnitudes can be
opposites modulo q only at zero. This is arithmetic, not a point-key theorem. -/
theorem no_nonzero_signed_alias (q m a b : Nat)
    (ha : a < m) (hb : b < m) (hspan : 2 * (m - 1) < q)
    (hmod : (a + b) % q = 0) : a = 0 ∧ b = 0 := by
  have hab : a + b < q := by omega
  rw [Nat.mod_eq_of_lt hab] at hmod
  omega

end Research.SignedCoverage
