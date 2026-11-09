/-
  Part (b) of MathDB 347063: the Combine Smallest estimate.
-/
import ZeckChain

open Classical

set_option linter.unusedSimpArgs false

namespace Zeck

noncomputable def bL : ℝ := 1 / (2 * Real.log 2)

noncomputable def C0 : ℝ := 8 * bL ^ 2 + 40 * bL + 29 / Real.log 2

lemma log_two_pos' : 0 < Real.log 2 := Real.log_pos (by norm_num)

lemma bL_pos : 0 < bL := by
  unfold bL
  have := log_two_pos'
  positivity

lemma C0_pos : 0 < C0 := by
  unfold C0
  have h1 := bL_pos
  have h2 := log_two_pos'
  positivity

lemma D_start (n : ℕ) : D (start n) = 0 := by
  unfold start
  rw [D_single]
  have e : d 1 = 0 := by decide
  rw [e, mul_zero]

lemma exists_level (n : ℕ) (hn : 4 ≤ n) :
    ∃ J, F (2 * J + 2) ^ 2 ≤ n ∧ n < F (2 * J + 4) ^ 2 := by
  have hex : ∃ j, n < F (2 * j + 4) ^ 2 := by
    refine ⟨n, ?_⟩
    have h1 : 2 ^ (n + 2) ≤ F (2 * (n + 2)) := (F_pow_two_mul (n + 2)).1 (by omega)
    have h2 : n < 2 ^ n := Nat.lt_two_pow_self
    have h3 : (2 : ℕ) ^ n ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e : 2 * (n + 2) = 2 * n + 4 := by ring
    rw [e] at h1
    have h4 : F (2 * n + 4) ≤ F (2 * n + 4) ^ 2 := by
      have := F_pos (2 * n + 4)
      nlinarith
    omega
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0]
    simpa using hn
  · have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    have e : 2 * (Nat.find hex - 1) + 4 = 2 * Nat.find hex + 2 := by omega
    rw [e] at hmin
    exact not_lt.mp hmin

lemma sqrt_nat_ge_one (n : ℕ) (h : 1 ≤ n) : 1 ≤ Real.sqrt n := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
  have h2 := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_one] at h2

/-- The real-variable part of the Combine Smallest estimate. -/
lemma real_final (A Sq L χ T tail : ℝ) (hA0 : 0 ≤ A) (hSq : 1 ≤ Sq) (hl2L : Real.log 2 ≤ L)
    (hL2 : L ≤ 2 * Sq) (hA : A ≤ bL * L) (hχ : χ ≤ 2 * A + 3 * Sq)
    (hT : T ≤ χ * (2 * A + 7)) (htail : tail ≤ 2 * Sq) :
    16 * A + 2 * χ + T + tail ≤ C0 * Sq * L := by
  have hl2 := log_two_pos'
  have hb := bL_pos
  have hLpos : 0 < L := lt_of_lt_of_le hl2 hl2L
  have hA1 : 2 * χ + T ≤ (2 * A + 9) * (2 * A + 3 * Sq) := by
    have h1 : T ≤ χ * (2 * A + 7) := hT
    have h2 : χ * (2 * A + 9) ≤ (2 * A + 3 * Sq) * (2 * A + 9) :=
      mul_le_mul_of_nonneg_right hχ (by linarith)
    nlinarith
  have hexp : 16 * A + (2 * A + 9) * (2 * A + 3 * Sq) + 2 * Sq
      = 4 * A ^ 2 + 34 * A + 6 * A * Sq + 29 * Sq := by ring
  have t1 : 4 * A ^ 2 ≤ 8 * bL ^ 2 * Sq * L := by
    calc 4 * A ^ 2 ≤ 4 * (bL * L) ^ 2 := by gcongr
      _ = 4 * bL ^ 2 * L * L := by ring
      _ ≤ 4 * bL ^ 2 * L * (2 * Sq) := by gcongr
      _ = 8 * bL ^ 2 * Sq * L := by ring
  have t2 : 34 * A ≤ 34 * bL * Sq * L := by
    have h1 : 34 * A ≤ 34 * (bL * L) := by linarith
    have h2 : bL * L ≤ bL * L * Sq := by
      have : 0 ≤ bL * L := by positivity
      nlinarith
    nlinarith
  have t3 : 6 * A * Sq ≤ 6 * bL * Sq * L := by
    have h1 : A * Sq ≤ (bL * L) * Sq := by
      exact mul_le_mul_of_nonneg_right hA (by linarith)
    nlinarith
  have t4 : 29 * Sq ≤ 29 / Real.log 2 * Sq * L := by
    have h1 : 1 ≤ L / Real.log 2 := (one_le_div hl2).2 hl2L
    have e : 29 / Real.log 2 * Sq * L = 29 * Sq * (L / Real.log 2) := by
      field_simp
    rw [e]
    have h2 : 29 * Sq * 1 ≤ 29 * Sq * (L / Real.log 2) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  have hfinal : C0 * Sq * L = 8 * bL ^ 2 * Sq * L + 34 * bL * Sq * L + 6 * bL * Sq * L
      + 29 / Real.log 2 * Sq * L := by
    unfold C0
    ring
  calc 16 * A + 2 * χ + T + tail ≤ 16 * A + (2 * A + 9) * (2 * A + 3 * Sq) + 2 * Sq := by
        linarith
    _ = 4 * A ^ 2 + 34 * A + 6 * A * Sq + 29 * Sq := hexp
    _ ≤ 8 * bL ^ 2 * Sq * L + 34 * bL * Sq * L + 6 * bL * Sq * L
        + 29 / Real.log 2 * Sq * L := by linarith
    _ = C0 * Sq * L := hfinal.symm

theorem CS_large (n : ℕ) (hn : 1000 ≤ n) :
    |(CS n : ℝ) - combC * n| ≤ C0 * Real.sqrt n * Real.log n := by
  obtain ⟨J, hJ1, hJ2⟩ := exists_level n (by omega)
  obtain ⟨z, m, h, k, e, hz, hh, hT, hQ⟩ := chain n J hn hJ1 J (le_refl _)
  have hval : val (B z (2 * J) m h) = n := by
    have := hT.st.val_eq
    rw [val_start] at this
    exact this
  have hval2 : val z + m * F (2 * J + 2) + h * F (2 * J + 4) = n := by
    rw [val_B] at hval
    exact hval
  have hD : (D (B z (2 * J) m h) : ℝ) = e := by
    have := hT.dv
    rw [D_start, zero_add] at this
    rw [this]
  have hSteps : CS n = k + CSfrom (B z (2 * J) m h) := CSfrom_eq hT.st
  -- the real quantities
  have hnR : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hSq0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hSq1 : 1 ≤ Real.sqrt n := sqrt_nat_ge_one n (by omega)
  have hSqSq : (n : ℝ) = Real.sqrt n * Real.sqrt n :=
    (Real.mul_self_sqrt (Nat.cast_nonneg n)).symm
  have hl2 := log_two_pos'
  have hL2 : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by linarith)
  have hL1 : Real.log n ≤ 2 * Real.sqrt n := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt n by linarith)
    have h2 := Real.log_sqrt (Nat.cast_nonneg n : (0:ℝ) ≤ (n : ℝ))
    linarith
  have hA : (J : ℝ) + 1 ≤ bL * Real.log n := by
    have hpow : 2 ^ (J + 1) ≤ F (2 * J + 2) := by
      have := (F_pow_two_mul (J + 1)).1 (by omega)
      have e : 2 * (J + 1) = 2 * J + 2 := by ring
      rwa [e] at this
    have hsq : (2 ^ (J + 1)) ^ 2 ≤ n :=
      le_trans (Nat.pow_le_pow_left hpow 2) hJ1
    have hr : ((2 : ℝ) ^ (J + 1)) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hsq
    have hlog : ((J : ℝ) + 1) * (2 * Real.log 2) ≤ Real.log n := by
      have h1 := Real.log_le_log (by positivity) hr
      have h2 : Real.log (((2 : ℝ) ^ (J + 1)) ^ 2) = ((J : ℝ) + 1) * (2 * Real.log 2) := by
        rw [Real.log_pow, Real.log_pow]
        push_cast
        ring
      rw [h2] at h1
      exact h1
    have e : bL * Real.log n = Real.log n / (2 * Real.log 2) := by
      unfold bL
      ring
    rw [e, le_div_iff₀ (by positivity)]
    exact hlog
  -- the bound on the number of chips
  have hFb0 : (0 : ℝ) < (F (2 * J + 4) : ℝ) := F_cast_pos _
  have hF20 : (0 : ℝ) < (F (2 * J + 2) : ℝ) := F_cast_pos _
  have hFb2 : (F (2 * J + 4) : ℝ) ≤ 3 * (F (2 * J + 2) : ℝ) := by
    exact_mod_cast F_add_two_le (2 * J)
  have hJ2R : (n : ℝ) < (F (2 * J + 4) : ℝ) ^ 2 := by exact_mod_cast hJ2
  have hSqFb : Real.sqrt n < (F (2 * J + 4) : ℝ) := (Real.sqrt_lt' hFb0).2 hJ2R
  have hmF : (m : ℝ) * (F (2 * J + 2) : ℝ) ≤ n := by
    have : m * F (2 * J + 2) ≤ n := by omega
    exact_mod_cast this
  have hm3 : (m : ℝ) ≤ 3 * Real.sqrt n := by
    have h1 : (n : ℝ) ≤ Real.sqrt n * (F (2 * J + 4) : ℝ) := by
      have h0 := mul_le_mul_of_nonneg_left (le_of_lt hSqFb) hSq0
      linarith [hSqSq]
    have h2 : Real.sqrt n * (F (2 * J + 4) : ℝ) ≤ Real.sqrt n * (3 * (F (2 * J + 2) : ℝ)) :=
      mul_le_mul_of_nonneg_left hFb2 hSq0
    have h3 : (m : ℝ) * (F (2 * J + 2) : ℝ) ≤ (3 * Real.sqrt n) * (F (2 * J + 2) : ℝ) := by
      nlinarith
    exact le_of_mul_le_mul_right h3 hF20
  have hchips : (chips (B z (2 * J) m h) : ℝ) ≤ 2 * ((J : ℝ) + 1) + 3 * Real.sqrt n := by
    have h1 := hz.chips_le _ _
    have h2 := chips_B z (2 * J) m h
    have h3 : chips (B z (2 * J) m h) ≤ 2 * J + m + 2 := by omega
    have h4 : (chips (B z (2 * J) m h) : ℝ) ≤ 2 * (J : ℝ) + (m : ℝ) + 2 := by exact_mod_cast h3
    linarith
  have hchips0 : (0 : ℝ) ≤ (chips (B z (2 * J) m h) : ℝ) := Nat.cast_nonneg _
  -- the remaining moves
  have hT1 : (CSfrom (B z (2 * J) m h) : ℝ) ≤
      (chips (B z (2 * J) m h) : ℝ) * (2 * ((J : ℝ) + 1) + 7) := by
    have h1 := CSfrom_le_Phi (B z (2 * J) m h)
    have h2 := Phi_le_chips_mul (B z (2 * J) m h) (2 * J + 6) (by
      intro i hi
      unfold B
      rw [Finsupp.add_apply, hz.top i (by omega), W_above (by omega)])
    push_cast at h2
    have e : (2 : ℝ) * (J : ℝ) + 6 + 3 = 2 * ((J : ℝ) + 1) + 7 := by ring
    rw [e] at h2
    linarith
  have hT0 : (0 : ℝ) ≤ (CSfrom (B z (2 * J) m h) : ℝ) := Nat.cast_nonneg _
  -- the tail of the series
  have htail0 := aT_tail_nonneg J
  have htail1 := aT_tail_le J
  have htail2 : (n : ℝ) * ∑' t, aT (t + J) ≤ 2 * Real.sqrt n := by
    have h1 : (n : ℝ) * ∑' t, aT (t + J) ≤ n * (2 * aT J) :=
      mul_le_mul_of_nonneg_left htail1 (Nat.cast_nonneg n)
    have h2 : (n : ℝ) * (2 * aT J) = 2 * ((n : ℝ) / (F (2 * J + 4) : ℝ)) := by
      unfold aT
      ring
    have h3 : (n : ℝ) / (F (2 * J + 4) : ℝ) ≤ Real.sqrt n := by
      rw [div_le_iff₀ hFb0]
      have h4 : Real.sqrt n * Real.sqrt n ≤ Real.sqrt n * (F (2 * J + 4) : ℝ) :=
        mul_le_mul_of_nonneg_left (le_of_lt hSqFb) hSq0
      linarith [hSqSq]
    linarith
  -- the counter and the assembly
  have hDA := D_approx (B z (2 * J) m h)
  rw [hval, hD] at hDA
  have hCS : (CS n : ℝ) = k + (CSfrom (B z (2 * J) m h) : ℝ) := by
    rw [hSteps]
    push_cast
    ring
  have hc : combC * (n : ℝ) = (n : ℝ) / 2 + rho * n + n * Ssum J + n * ∑' t, aT (t + J) := by
    rw [combC_eq, aT_split J]
    unfold rho
    ring
  rw [hCS, hc]
  rw [abs_le] at hQ hDA
  obtain ⟨hQ1, hQ2⟩ := hQ
  obtain ⟨hDA1, hDA2⟩ := hDA
  have hfin := real_final ((J : ℝ) + 1) (Real.sqrt n) (Real.log n)
    (chips (B z (2 * J) m h) : ℝ) (CSfrom (B z (2 * J) m h) : ℝ) ((n : ℝ) * ∑' t, aT (t + J))
    (by positivity) hSq1 hL2 hL1 hA hchips hT1 htail2
  have htail3 : 0 ≤ (n : ℝ) * ∑' t, aT (t + J) := mul_nonneg (Nat.cast_nonneg n) htail0
  rw [abs_le]
  constructor <;> linarith

lemma CS_nonneg_le (n : ℕ) : (CS n : ℝ) ≤ 3 * n := by
  have h := CSfrom_le_Phi (start n)
  rw [← CS_eq, Phi_start] at h
  have h1 := phi_sq
  have h2 := phi_lt_two
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith

/-- The Combine Smallest estimate for every `n ≥ 2`. -/
theorem CS_estimate :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → |(CS n : ℝ) - combC * n| ≤ C * Real.sqrt n * Real.log n := by
  have hl2 := log_two_pos'
  refine ⟨C0 + 3000 / Real.log 2, fun n hn => ?_⟩
  have hC0 := C0_pos
  have hq0 : (0 : ℝ) < 3000 / Real.log 2 := by positivity
  have hSq1 : 1 ≤ Real.sqrt n := sqrt_nat_ge_one n (by omega)
  have hL : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hL0 : 0 ≤ Real.log n := le_of_lt (lt_of_lt_of_le hl2 hL)
  have hprod : 0 ≤ Real.sqrt n * Real.log n := mul_nonneg (by linarith) hL0
  by_cases hbig : 1000 ≤ n
  · have h := CS_large n hbig
    have e : (C0 + 3000 / Real.log 2) * Real.sqrt n * Real.log n
        = C0 * Real.sqrt n * Real.log n + 3000 / Real.log 2 * (Real.sqrt n * Real.log n) := by
      ring
    rw [e]
    have : 0 ≤ 3000 / Real.log 2 * (Real.sqrt n * Real.log n) := mul_nonneg (le_of_lt hq0) hprod
    linarith
  · have hsmall : (n : ℝ) ≤ 1000 := by
      have : n ≤ 1000 := by omega
      exact_mod_cast this
    have hle := CS_nonneg_le n
    have hge : (0 : ℝ) ≤ (CS n : ℝ) := Nat.cast_nonneg _
    have hbr := combC_bracket
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hc1 : combC * (n : ℝ) ≤ 2 * n := by nlinarith [hbr.2]
    have hc2 : 0 ≤ combC * (n : ℝ) := by nlinarith [hbr.1]
    have habs : |(CS n : ℝ) - combC * n| ≤ 3000 := by
      rw [abs_le]
      constructor <;> linarith
    have hprod1 : Real.log 2 ≤ Real.sqrt n * Real.log n := by nlinarith
    have hlast : (3000 : ℝ) ≤ 3000 / Real.log 2 * (Real.sqrt n * Real.log n) := by
      have h1 : 1 ≤ (Real.sqrt n * Real.log n) / Real.log 2 := (one_le_div hl2).2 hprod1
      have e : 3000 / Real.log 2 * (Real.sqrt n * Real.log n)
          = 3000 * ((Real.sqrt n * Real.log n) / Real.log 2) := by
        field_simp
      rw [e]
      linarith
    have e : (C0 + 3000 / Real.log 2) * Real.sqrt n * Real.log n
        = C0 * (Real.sqrt n * Real.log n) + 3000 / Real.log 2 * (Real.sqrt n * Real.log n) := by
      ring
    rw [e]
    have : 0 ≤ C0 * (Real.sqrt n * Real.log n) := mul_nonneg (le_of_lt hC0) hprod
    linarith

end Zeck
