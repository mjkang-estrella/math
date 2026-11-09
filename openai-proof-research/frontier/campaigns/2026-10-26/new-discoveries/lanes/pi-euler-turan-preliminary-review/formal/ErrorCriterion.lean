import Mathlib
noncomputable section
namespace EulerTuran
lemma paired_power_identity (A B : ℝ) (m : ℕ) :
    (A^2 + A*B + B^2) * (A^(m+1) - B^(m+1)) -
      (A^(m+3) - B^(m+3)) = A*B*(A+B)*(A^m-B^m) := by
  simp only [pow_succ]
  ring
lemma paired_power_contraction {A B : ℝ} (hB : 0 ≤ B) (hBA : B ≤ A)
    (hA : A ≤ 1/3) (m : ℕ) :
    A^(m+3)-B^(m+3) ≤ (A^(m+1)-B^(m+1))/3 := by
  have hAp : 0 ≤ A := hB.trans hBA
  have hp : 0 ≤ A^m-B^m := sub_nonneg.mpr (pow_le_pow_left₀ hB hBA m)
  have hd : 0 ≤ A^(m+1)-B^(m+1) :=
    sub_nonneg.mpr (pow_le_pow_left₀ hB hBA (m+1))
  have hAA : A^2 ≤ (1/3:ℝ)^2 := by gcongr
  have hBB : B^2 ≤ (1/3:ℝ)^2 := by gcongr; exact hBA.trans hA
  have hAB : A*B ≤ (1/3:ℝ)^2 := by
    calc A*B ≤ (1/3:ℝ)*(1/3) := by gcongr; exact hBA.trans hA
         _ = _ := by ring
  have hh := mul_nonneg (mul_nonneg (mul_nonneg hAp hB) (by linarith : 0 ≤ A+B)) hp
  rw [← paired_power_identity A B m] at hh
  have ht : (A^2+A*B+B^2) * (A^(m+1)-B^(m+1)) ≤
      (1/3:ℝ) * (A^(m+1)-B^(m+1)) :=
    mul_le_mul_of_nonneg_right (by nlinarith) hd
  nlinarith
lemma same_odd_sign {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (_ha1 : a < 1) (_hb1 : b < 1)
    (hc1 : c < 1) (hd1 : d < 1) :
    0 < a+b+c+d - (a*d-b*c) ∧ 0 < a+b+c+d + (a*d-b*c) := by
  have h1 := mul_pos ha (sub_pos.mpr hd1)
  have h2 := mul_pos hb (sub_pos.mpr hc1)
  have h3 := mul_pos hb hc
  have h4 := mul_pos ha hd
  constructor <;> nlinarith
lemma same_even_sign {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (ha1 : a < 1)
    (hba : b ≤ a/3) (hca : c ≤ a/3) :
    0 < a+d-b-c - (a*d-b*c) ∧ 0 < a+d-b-c + (a*d-b*c) := by
  have h1 := mul_pos hd (sub_pos.mpr ha1)
  have h2 := mul_pos hb hc
  have h3 := mul_pos ha hd
  have hbc : b*c ≤ (a/3)*(a/3) := by gcongr
  constructor <;> nlinarith [sq_nonneg a]
lemma mixed_sign {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hb1 : b < 1)
    (hca : c ≤ a/3) (hdb : d ≤ b/3) :
    0 < a+b-c-d - (a*d-b*c) ∧ 0 < a+b-c-d + (a*d-b*c) := by
  have h1 := mul_pos ha (sub_pos.mpr hb1)
  have h2 := mul_pos hb hc
  have h3 := mul_pos ha hd
  have had : a*d ≤ a*(b/3) := by gcongr
  have hbc : b*c ≤ b*(a/3) := by gcongr
  constructor <;> nlinarith
lemma even_shift_nonincreasing {c : ℕ → ℝ} (hc : ∀ n, 0 < c n)
    (hs : ∀ n, c (n+2) ≤ c n/3) (n m : ℕ) : c (n+2*m) ≤ c n := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hh := hs (n+2*m)
    rw [show n+2*m+2 = n+2*(m+1) by omega] at hh
    have hp := hc (n+2*m)
    linarith
lemma even_shift_contraction {c : ℕ → ℝ} (hc : ∀ n, 0 < c n)
    (hs : ∀ n, c (n+2) ≤ c n/3) {k : ℕ} (hk : Even k) (hkpos : 0 < k)
    (n : ℕ) : c (n+k) ≤ c n/3 := by
  obtain ⟨m, hm⟩ := hk
  have hmpos : 0 < m := by omega
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
  have hh := hs (n+2*l)
  have hnon := even_shift_nonincreasing hc hs n l
  have hid : n+k = n+2*l+2 := by omega
  rw [hid]
  linarith
end EulerTuran
