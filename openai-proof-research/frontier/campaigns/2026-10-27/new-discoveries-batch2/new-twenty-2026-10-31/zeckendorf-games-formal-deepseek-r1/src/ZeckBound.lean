/-
  Part (a) of MathDB 347063, the exact Split Smallest count.

  Every Phase-1 move (A1 or split) lowers Phi by exactly 1; every Cons i lowers it
  by exactly i >= 2.  Hence the number of moves is at most phi^2 * n, with the gap
  Phi(final) + (extra drops of combining moves).
-/
import ZeckPotential

open Classical

namespace Zeck

lemma phi_gt_one : 1 < phi := by
  unfold phi
  have h0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith

lemma phi_lt_two : phi < 2 := by
  unfold phi
  have h0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith

lemma psi_pos : 0 < psi := by
  unfold psi
  linarith [phi_gt_one]

lemma psi_lt_one : psi < 1 := by
  unfold psi
  linarith [phi_lt_two]

lemma abs_s_lt_one : |s| < 1 := by
  unfold s
  rw [abs_lt]
  constructor <;> linarith [phi_gt_one, phi_lt_two]

lemma abs_s_pow_le_one (i : ℕ) : |s ^ i| ≤ 1 := by
  rw [abs_pow]
  induction i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have h0 : 0 ≤ |s| := abs_nonneg s
    nlinarith [abs_s_lt_one, ih, h0]

lemma w_pos (i : ℕ) : 0 < w i := by
  have hle : |psi * s ^ i| ≤ psi := by
    rw [abs_mul, abs_of_pos psi_pos]
    nlinarith [abs_s_pow_le_one i, psi_pos]
  have h2 : -psi ≤ psi * s ^ i := by
    linarith [neg_abs_le (psi * s ^ i), hle]
  unfold w
  have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  linarith [psi_lt_one, h2, hi]

lemma Phi_nonneg (a : Pos) : 0 ≤ Phi a := by
  unfold Phi
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (le_of_lt (w_pos i)))

/-- A move always drops the potential by at least one. -/
lemma dropSS_ge_one (a : Pos) (h : hasMove a) : 1 ≤ dropSS a := by
  unfold dropSS
  cases hsp : smallestSplit a with
  | some _ => simp
  | none =>
    dsimp only
    split_ifs with ha1
    · simp
    · cases hco : smallestCons a with
      | some i =>
        dsimp only
        have h2 : 2 ≤ i := (smallestCons_some_spec a hco).1.1
        omega
      | none =>
        dsimp only
        exfalso
        have hs : ¬ ∃ i, legalSplit a i := (smallestSplit_none_iff a).1 hsp
        have hc : ¬ ∃ i, legalCons a i := (smallestCons_none_iff a).1 hco
        rcases h with hA | hC | hS
        · exact ha1 hA
        · obtain ⟨i, hi⟩ := hC
          exact hc ⟨i, hi⟩
        · obtain ⟨i, hi⟩ := hS
          exact hs ⟨i, hi⟩

lemma SS_move_ge_one (n : ℕ) (j : ℕ) (hj : j < SS n) :
    (1 : ℝ) ≤ (dropSS (run stepSS (start n) j) : ℝ) := by
  have hmove : hasMove (run stepSS (start n) j) := gameLen_min stepSS stepSS_drop (start n) j hj
  exact_mod_cast dropSS_ge_one _ hmove

lemma sum_one_range (k : ℕ) : Finset.sum (Finset.range k) (fun _ => (1 : ℝ)) = (k : ℝ) := by
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-- The exact Split Smallest identity. -/
lemma SS_eq (n : ℕ) :
    (SS n : ℝ) = phi ^ 2 * n - Phi (run stepSS (start n) (SS n))
      - Finset.sum (Finset.range (SS n))
          (fun j => (dropSS (run stepSS (start n) j) : ℝ) - 1) := by
  have h := Phi_run n (SS n)
  have hstart := Phi_start n
  have h1 := sum_one_range (SS n)
  have hsplit : Finset.sum (Finset.range (SS n))
        (fun j => (dropSS (run stepSS (start n) j) : ℝ) - 1)
      = Finset.sum (Finset.range (SS n)) (fun j => (dropSS (run stepSS (start n) j) : ℝ)) - (SS n : ℝ) := by
    rw [Finset.sum_sub_distrib, h1]
  linarith [h, hstart, hsplit]

/-- Every drop is at least one, so the gap is nonnegative. -/
lemma SS_excess_nonneg (n : ℕ) :
    0 ≤ Finset.sum (Finset.range (SS n))
      (fun j => (dropSS (run stepSS (start n) j) : ℝ) - 1) := by
  apply Finset.sum_nonneg
  intro j hj
  have hj' : j < SS n := Finset.mem_range.1 hj
  linarith [SS_move_ge_one n j hj']

/-- Part (a), upper half: `SS n ≤ phi^2 n`. -/
theorem SS_le_phi_sq (n : ℕ) : (SS n : ℝ) ≤ phi ^ 2 * n := by
  have hid := SS_eq n
  have hex := SS_excess_nonneg n
  have hpos := Phi_nonneg (run stepSS (start n) (SS n))
  linarith

/-- The same bound, in the shape used by the reviewer: the deficit from `phi^2 n`
is exactly the final potential plus the extra drops. -/
lemma SS_deficit (n : ℕ) :
    phi ^ 2 * n - (SS n : ℝ) = Phi (run stepSS (start n) (SS n))
      + Finset.sum (Finset.range (SS n))
          (fun j => (dropSS (run stepSS (start n) j) : ℝ) - 1) := by
  have hid := SS_eq n
  linarith

end Zeck
