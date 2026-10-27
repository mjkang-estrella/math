import ErrorCriterion
noncomputable section
namespace EulerTuran
def corrected (c : ℕ → ℝ) (n : ℕ) : ℝ := 1 + (-1 : ℝ)^(n+1)*c n
/-- Supporting theorem only: the actual Euler identity must still be proved. -/
theorem alternating_turan_of_contraction {c : ℕ → ℝ}
    (hc : ∀ n, 0 < c n ∧ c n < 1) (hstep : ∀ n, c (n+2) ≤ c n/3)
    (n j k : ℕ) (hjpos : 0 < j) (hkpos : 0 < k) :
    0 < (-1 : ℝ)^(n+1) *
      (corrected c n * corrected c (n+j+k) - corrected c (n+j) * corrected c (n+k)) := by
  have hp : ∀ n, 0 < c n := fun n => (hc n).1
  rcases Nat.even_or_odd j with hj | hj
  · rcases Nat.even_or_odd k with hk | hk
    · have hb := even_shift_contraction hp hstep hj hjpos n
      have hd := even_shift_contraction hp hstep hk hkpos n
      have hh := same_even_sign (hp n) (hp (n+j)) (hp (n+k)) (hp (n+j+k))
        (hc n).2 hb hd
      rcases Nat.even_or_odd n with hn | hn
      · simp only [corrected, pow_add, hn.neg_one_pow, hj.neg_one_pow, hk.neg_one_pow,
          pow_one]
        nlinarith [hh.1, hh.2]
      · simp only [corrected, pow_add, hn.neg_one_pow, hj.neg_one_pow, hk.neg_one_pow,
          pow_one]
        nlinarith [hh.1, hh.2]
    · have hb := even_shift_contraction hp hstep hj hjpos n
      have hd := even_shift_contraction hp hstep hj hjpos (n+k)
      rw [show n+k+j = n+j+k by omega] at hd
      have hh := mixed_sign (hp n) (hp (n+k)) (hp (n+j)) (hp (n+j+k))
        (hc (n+k)).2 hb hd
      rcases Nat.even_or_odd n with hn | hn
      · simp only [corrected, pow_add, hn.neg_one_pow, hj.neg_one_pow, hk.neg_one_pow,
          pow_one]
        nlinarith [hh.1, hh.2]
      · simp only [corrected, pow_add, hn.neg_one_pow, hj.neg_one_pow, hk.neg_one_pow,
          pow_one]
        nlinarith [hh.1, hh.2]
  · rcases Nat.even_or_odd k with hk | hk
    · have hb := even_shift_contraction hp hstep hk hkpos n
      have hd := even_shift_contraction hp hstep hk hkpos (n+j)
      have hh := mixed_sign (hp n) (hp (n+j)) (hp (n+k)) (hp (n+j+k))
        (hc (n+j)).2 hb hd
      rcases Nat.even_or_odd n with hn | hn
      · simp only [corrected, pow_add, hn.neg_one_pow, hj.neg_one_pow, hk.neg_one_pow,
          pow_one]
        nlinarith [hh.1, hh.2]
      · simp only [corrected, pow_add, hn.neg_one_pow, hj.neg_one_pow, hk.neg_one_pow,
          pow_one]
        nlinarith [hh.1, hh.2]
    · have hh := same_odd_sign (hp n) (hp (n+j)) (hp (n+k)) (hp (n+j+k))
        (hc n).2 (hc (n+j)).2 (hc (n+k)).2 (hc (n+j+k)).2
      rcases Nat.even_or_odd n with hn | hn
      · simp only [corrected, pow_add, hn.neg_one_pow, hj.neg_one_pow, hk.neg_one_pow,
          pow_one]
        nlinarith [hh.1, hh.2]
      · simp only [corrected, pow_add, hn.neg_one_pow, hj.neg_one_pow, hk.neg_one_pow,
          pow_one]
        nlinarith [hh.1, hh.2]
end EulerTuran
