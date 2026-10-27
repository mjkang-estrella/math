import SourceDefs

namespace Davis

noncomputable section

theorem falling_succ (x : ℝ) (i : ℕ) :
    falling x (i + 1) = falling x i * (x - i) := by
  simp only [falling, Finset.prod_range_succ]

theorem weight_reverse {d i : ℕ} (hi : i ≤ d) (x : ℝ) :
    weight d (d - i) x = weight d i x := by
  simp only [weight, Nat.sub_sub_self hi]
  ring

theorem weight_step (d i : ℕ) (x : ℝ) :
    (i + 1 : ℝ) * weight (d + 1) (i + 1) x = (x - i) ^ 2 * weight d i x := by
  simp only [weight, Nat.add_sub_add_right, falling_succ, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hi : (i + 1 : ℝ) ≠ 0 := by positivity
  have hf : (Nat.factorial i : ℝ) ≠ 0 := by positivity
  have hg : (Nat.factorial (d - i) : ℝ) ≠ 0 := by positivity
  field_simp

theorem weight_balance {d i : ℕ} (hi : i < d) (x : ℝ) :
    ((d - i : ℕ) : ℝ) * (x - i) ^ 2 * weight d i x =
      (i + 1 : ℝ) * (x - (d : ℝ) + (i + 1)) ^ 2 * weight d (i + 1) x := by
  have he : d - i = d - (i + 1) + 1 := by omega
  have hfact := Nat.factorial_succ (d - (i + 1))
  have hfall := falling_succ x (d - (i + 1))
  have hcast : ((d - (i + 1) : ℕ) : ℝ) = (d : ℝ) - (i + 1) := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  unfold weight
  rw [he, hfact, hfall, falling_succ]
  simp only [Nat.factorial_succ, Nat.cast_add, Nat.cast_one, Nat.cast_mul, hcast]
  have hf : (Nat.factorial i : ℝ) ≠ 0 := by positivity
  have hg : (Nat.factorial (d - (i + 1)) : ℝ) ≠ 0 := by positivity
  have hii : (i + 1 : ℝ) ≠ 0 := by positivity
  have hd : ((d : ℝ) - (i + 1) + 1) ≠ 0 := by
    have hir : (i : ℝ) < d := by exact_mod_cast hi
    linarith
  field_simp
  ring

end

end Davis
