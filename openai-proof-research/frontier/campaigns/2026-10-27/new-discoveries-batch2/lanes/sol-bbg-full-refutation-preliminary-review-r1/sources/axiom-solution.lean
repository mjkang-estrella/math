import Mathlib

open scoped Classical

/-- The value μ(π) ≈ 7.10321 (see arXiv:1912.06345) -/
noncomputable abbrev muPi : ℝ := 7.10321

def PiIrrBound : Prop :=
  ∃ (C : ℝ) (Q₀ : ℕ), 0 < C ∧ ∀ (p : ℤ) (q : ℕ), 0 < q → Q₀ ≤ q →
    C / (q : ℝ) ^ muPi < |Real.pi - (p : ℝ) / (q : ℝ)|

noncomputable def a (n : ℝ) : ℝ := 2 / 3 + 1 / 3 * Real.sin n

lemma a_nonneg (n : ℝ) : 0 ≤ a n := by
  unfold a
  linarith [Real.neg_one_le_sin n]

lemma a_le_one (n : ℝ) : a n ≤ 1 := by
  unfold a
  linarith [Real.sin_le_one n]

lemma term_nonneg (n : ℕ+) : 0 ≤ a (n : ℝ) ^ (n : ℕ) / (n : ℝ) :=
  div_nonneg (pow_nonneg (a_nonneg _) _) (Nat.cast_nonneg' _)

noncomputable def y_of (n : ℝ) : ℝ :=
  let x := n - Real.pi / 2
  x - 2 * Real.pi * ⌊x / (2 * Real.pi) + 1/2⌋

lemma y_of_mem_Icc (n : ℝ) : y_of n ∈ Set.Icc (-Real.pi) Real.pi := by
  unfold y_of
  simp only [Set.mem_Icc]
  set x := n - Real.pi / 2
  set t := x / (2 * Real.pi) + 1 / 2
  set k := ⌊t⌋
  have hk_le : (k : ℝ) ≤ t := Int.floor_le t
  have hk_lt : t < k + 1 := Int.lt_floor_add_one t
  have hx_eq : x = 2 * Real.pi * t - Real.pi := by
    rw [show t = x / (2 * Real.pi) + 1 / 2 from rfl]
    field_simp
    ring
  constructor <;> nlinarith [Real.pi_pos]

noncomputable def k_of (n : ℝ) : ℤ :=
  ⌊(n - Real.pi / 2) / (2 * Real.pi) + 1/2⌋

lemma y_of_spec (n : ℝ) : n - Real.pi / 2 = 2 * Real.pi * k_of n + y_of n := by
  simp only [y_of, k_of]
  ring

lemma sin_eq_cos_y (n : ℝ) : Real.sin n = Real.cos (y_of n) := by
  rw [show Real.sin n = Real.cos (n - Real.pi / 2) from by rw [Real.cos_sub_pi_div_two]]
  simp only [y_of]
  set x := n - Real.pi / 2
  conv_rhs =>
    rw [show x - 2 * Real.pi * ↑⌊x / (2 * Real.pi) + 1 / 2⌋ =
      x - ↑⌊x / (2 * Real.pi) + 1 / 2⌋ * (2 * Real.pi) from by ring]
  rw [Real.cos_sub_int_mul_two_pi]

lemma one_sub_sin_ge (n : ℝ) :
    2 / Real.pi ^ 2 * (y_of n) ^ 2 ≤ 1 - Real.sin n := by
  rw [sin_eq_cos_y]
  linarith [Real.cos_le_one_sub_mul_cos_sq
    (abs_le.mpr ⟨(y_of_mem_Icc n).1, (y_of_mem_Icc n).2⟩)]

lemma one_sub_pow_le_exp (u : ℝ) (n : ℕ) (hu1 : u ≤ 1) :
    (1 - u) ^ n ≤ Real.exp (-(n : ℝ) * u) := by
  calc (1 - u) ^ n
      ≤ (Real.exp (-u)) ^ n :=
        pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-u)]) _
    _ = Real.exp (-(n : ℝ) * u) := by
        rw [← Real.exp_nat_mul]
        ring_nf

lemma a_pow_le_exp (n : ℕ+) :
    a (n : ℝ) ^ (n : ℕ) ≤
      Real.exp (-(2 / (3 * Real.pi ^ 2)) * (n : ℝ) * (y_of (n : ℝ)) ^ 2) := by
  set u := (1 - Real.sin (n : ℝ)) / 3 with hu_def
  have hu1 : u ≤ 1 := by linarith [Real.neg_one_le_sin (n : ℝ)]
  rw [show a (n : ℝ) = 1 - u from by
      unfold a
      ring]
  have hu_ge : 2 / (3 * Real.pi ^ 2) * (y_of (n : ℝ)) ^ 2 ≤ u := by
    linarith [div_le_div_of_nonneg_right (one_sub_sin_ge (n : ℝ)) (by norm_num : (0 : ℝ) ≤ 3),
      show 2 / (3 * Real.pi ^ 2) * (y_of (n : ℝ)) ^ 2 =
        2 / Real.pi ^ 2 * (y_of (n : ℝ)) ^ 2 / 3 from by ring]
  calc (1 - u) ^ (n : ℕ)
      ≤ Real.exp (-(↑(n : ℕ) : ℝ) * u) := one_sub_pow_le_exp u (n : ℕ) hu1
    _ ≤ Real.exp (-(2 / (3 * Real.pi ^ 2)) * (n : ℝ) * (y_of (n : ℝ)) ^ 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hu_ge (Nat.cast_nonneg (n : ℕ))]

noncomputable def c₀ : ℝ := 2 / (3 * Real.pi ^ 2)

lemma c₀_pos : 0 < c₀ := by
  unfold c₀
  positivity

noncomputable def good (n : ℕ+) : Prop := (n : ℝ) ^ (-(1/4 : ℝ)) ≤ |y_of (n : ℝ)|

private lemma good_y_sq_bound' (n : ℕ+) (hg : good n) :
    (n : ℝ) ^ ((1 : ℝ)/2) ≤ (n : ℝ) * (y_of (n : ℝ)) ^ 2 := by
  unfold good at hg
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr n.pos
  have hsq : (n : ℝ) ^ (-(1/2 : ℝ)) ≤ (y_of (n : ℝ)) ^ 2 := by
    have h1 := sq_le_sq' (by linarith [Real.rpow_nonneg hn_pos.le (-(1/4 : ℝ))]) hg
    rw [sq_abs] at h1
    linarith [show ((n : ℝ) ^ (-(1/4 : ℝ))) ^ 2 = (n : ℝ) ^ (-(1/2 : ℝ)) from by
      rw [← Real.rpow_natCast ((n : ℝ) ^ (-(1/4 : ℝ))) 2, ← Real.rpow_mul hn_pos.le]
      norm_num]
  rw [show (n : ℝ) ^ ((1 : ℝ)/2) = (n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) from by
    rw [show (n : ℝ) ^ ((1 : ℝ)/2) = (n : ℝ) ^ (1 + -(1/2 : ℝ)) from by norm_num,
      Real.rpow_add hn_pos, Real.rpow_one]]
  exact mul_le_mul_of_nonneg_left hsq hn_pos.le

lemma good_exp_bound (n : ℕ+) (hg : good n) :
    a (n : ℝ) ^ (n : ℕ) / (n : ℝ) ≤ Real.exp (-c₀ * (n : ℝ) ^ (1/2 : ℝ)) / (n : ℝ) := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_pos.mpr n.pos).le
  calc a (n : ℝ) ^ (n : ℕ)
      ≤ Real.exp (-(2 / (3 * Real.pi ^ 2)) * (n : ℝ) * (y_of (n : ℝ)) ^ 2) := a_pow_le_exp n
    _ ≤ Real.exp (-c₀ * (n : ℝ) ^ ((1 : ℝ)/2)) := by
        apply Real.exp_le_exp.mpr
        unfold c₀
        nlinarith [good_y_sq_bound' n hg, (show (0 : ℝ) < 2 / (3 * Real.pi ^ 2) by positivity)]

section exp_summability
open Real

private lemma exp_sqrt_div_le_inv_sq (c : ℝ) (hc : 0 < c) (n : ℕ+) :
    Real.exp (-c * (n : ℝ) ^ (1/2 : ℝ)) / (n : ℝ) ≤
    4 / (c ^ 2 * (n : ℝ) ^ 2) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr n.pos
  set s := c * (n : ℝ) ^ (1/2 : ℝ) with hs_def
  have hs_nonneg : 0 ≤ s := mul_nonneg hc.le (rpow_nonneg hn_pos.le _)
  have h_rpow_sq : ((n : ℝ) ^ (1/2 : ℝ)) ^ 2 = (n : ℝ) := by
    rw [← rpow_natCast ((n : ℝ) ^ (1/2 : ℝ)) 2, ← rpow_mul hn_pos.le]
    norm_num
  have h1 : c ^ 2 * (n : ℝ) / 4 ≤ exp s := by
    suffices s ^ 2 / 4 ≤ exp s by
      rwa [show s ^ 2 = c ^ 2 * (n : ℝ) from by rw [hs_def, mul_pow, h_rpow_sq]] at this
    linarith [Real.add_one_le_exp (s / 2),
      sq_le_sq' (by linarith [Real.exp_nonneg (s / 2)]) (Real.add_one_le_exp (s / 2)),
      sq_nonneg (s / 2), sq_nonneg (s / 2 + 1),
      show (Real.exp (s / 2)) ^ 2 = exp s from by
        rw [sq, ← Real.exp_add]
        ring_nf]
  rw [div_le_div_iff₀ hn_pos (mul_pos (sq_pos_of_pos hc) (sq_pos_of_pos hn_pos)),
    show (-c * (n : ℝ) ^ (1/2 : ℝ)) = -s from by
      rw [hs_def]
      ring,
    exp_neg, inv_mul_le_iff₀ (exp_pos s)]
  nlinarith

lemma summable_exp_sqrt_div (c : ℝ) (hc : 0 < c) :
    Summable fun n : ℕ+ ↦ Real.exp (-c * (n : ℝ) ^ (1/2 : ℝ)) / (n : ℝ) := by
  apply Summable.of_nonneg_of_le
    (fun n => div_nonneg (le_of_lt (Real.exp_pos _)) (Nat.cast_nonneg' _))
    (exp_sqrt_div_le_inv_sq c hc)
  have h : Summable (fun n : ℕ ↦ 4 / (c ^ 2 * (n : ℝ) ^ 2)) := by
    rw [show (fun n : ℕ ↦ 4 / (c ^ 2 * (n : ℝ) ^ 2)) =
      fun n : ℕ ↦ (4 / c ^ 2) * ((n : ℝ) ^ 2)⁻¹ from by
        ext n
        field_simp]
    exact (Real.summable_nat_pow_inv.mpr (by norm_num)).mul_left _
  exact h.comp_injective Subtype.val_injective

end exp_summability

lemma summable_good :
    Summable fun n : ℕ+ ↦ if good n then a (n : ℝ) ^ (n : ℕ) / (n : ℝ) else 0 :=
  Summable.of_nonneg_of_le
    (fun n => by split_ifs <;> [exact term_nonneg n; exact le_refl 0])
    (fun n => by split_ifs with h <;> [exact good_exp_bound n h; positivity])
    (summable_exp_sqrt_div c₀ c₀_pos)

lemma bad_trivial_bound (n : ℕ+) :
    a (n : ℝ) ^ (n : ℕ) / (n : ℝ) ≤ 1 / (n : ℝ) :=
  div_le_div_of_nonneg_right (pow_le_one₀ (a_nonneg _) (a_le_one _))
    (Nat.cast_pos.mpr n.pos).le

/-! ## Gap principle from PiIrrBound -/

private theorem pi_rational_approx_bound (n₁ n₂ k₁ k₂ : ℤ) (ε : ℝ)
    (hk : k₁ ≠ k₂)
    (h1 : |↑n₁ - (Real.pi / 2 + 2 * Real.pi * ↑k₁)| < ε)
    (h2 : |↑n₂ - (Real.pi / 2 + 2 * Real.pi * ↑k₂)| < ε) :
    |Real.pi - (↑n₂ - ↑n₁) / (2 * (↑k₂ - ↑k₁))| <
      ε / ((k₂ - k₁).natAbs : ℝ) := by
  have hkR : (↑k₂ : ℝ) - ↑k₁ ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hk.symm
  rw [show Real.pi - (↑n₂ - ↑n₁) / (2 * ((↑k₂ : ℝ) - ↑k₁)) =
      ((Real.pi / 2 + 2 * Real.pi * ↑k₂ - ↑n₂) -
       (Real.pi / 2 + 2 * Real.pi * ↑k₁ - ↑n₁)) / (2 * (↑k₂ - ↑k₁)) from by
    field_simp
    ring,
    show ((k₂ - k₁).natAbs : ℝ) = |(↑k₂ : ℝ) - ↑k₁| from by
      rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub],
    abs_div, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hD := abs_pos.mpr hkR
  rw [div_lt_div_iff₀ (by linarith : (0:ℝ) < 2 * |(↑k₂ : ℝ) - ↑k₁|) hD]
  nlinarith [hD, show |(Real.pi / 2 + 2 * Real.pi * ↑k₂ - ↑n₂) -
     (Real.pi / 2 + 2 * Real.pi * ↑k₁ - ↑n₁)| < 2 * ε from by grind]

private lemma gap_bound_from_irrationality
    (C ε D : ℝ) (hC : 0 < C) (hε : 0 < ε) (hD : 0 < D)
    (h : C / (2 * D) ^ muPi < ε / D) :
    (C / ((2 : ℝ) ^ muPi * ε)) ^ ((1 : ℝ) / (muPi - 1)) ≤ D := by
  rw [show (1 : ℝ) / (muPi - 1) = (muPi - 1)⁻¹ from one_div _,
    Real.rpow_inv_le_iff_of_pos (by positivity) hD.le (by positivity)]
  rw [show (2 * D) ^ muPi = (2 : ℝ) ^ muPi * D ^ muPi
    from Real.mul_rpow (by positivity) hD.le] at h
  rw [show D ^ muPi = D ^ (muPi - 1) * D from by
    conv_lhs => rw [show muPi = muPi - 1 + 1 from by ring]
    rw [Real.rpow_add hD, Real.rpow_one]] at h
  rw [show (2 : ℝ) ^ muPi * (D ^ (muPi - 1) * D) =
    ((2 : ℝ) ^ muPi * D ^ (muPi - 1)) * D from by ring,
    div_lt_div_iff₀ (by positivity) hD] at h
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ muPi * ε)]
  nlinarith [mul_comm (D ^ (muPi - 1)) (2 ^ muPi * ε),
    lt_of_mul_lt_mul_right (show C * D < ε * (2 ^ muPi * D ^ (muPi - 1)) * D by nlinarith) hD.le]

private lemma C_gap_epsilon_eq (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    (C / ((2 : ℝ) ^ muPi)) ^ ((1 : ℝ) / (muPi - 1)) *
      ε ^ (-(1 : ℝ) / (muPi - 1)) =
    (C / ((2 : ℝ) ^ muPi * ε)) ^ ((1 : ℝ) / (muPi - 1)) := by
  rw [show C / ((2 : ℝ) ^ muPi * ε) = C / (2 : ℝ) ^ muPi * ε⁻¹ from by field_simp,
    Real.mul_rpow (by positivity) (by positivity),
    show ε⁻¹ ^ ((1 : ℝ) / (muPi - 1)) = ε ^ (-(1 : ℝ) / (muPi - 1)) from by
      rw [show (ε⁻¹ : ℝ) = ε ^ (-(1 : ℝ)) from (Real.rpow_neg_one ε).symm,
        ← Real.rpow_mul hε.le]
      norm_num]

private lemma apply_PiIrrBound_to_approx
    (C : ℝ) (Q₀ : ℕ)
    (hPi : ∀ (p : ℤ) (q : ℕ), 0 < q → Q₀ ≤ q →
      C / (q : ℝ) ^ muPi < |Real.pi - (p : ℝ) / (q : ℝ)|)
    (n₁ n₂ k₁ k₂ : ℤ) (ε : ℝ)
    (hk : k₁ ≠ k₂)
    (hQ : Q₀ ≤ 2 * (k₂ - k₁).natAbs)
    (happrox : |Real.pi - (↑n₂ - ↑n₁) / (2 * (↑k₂ - ↑k₁))| <
      ε / ((k₂ - k₁).natAbs : ℝ)) :
    C / (2 * ((k₂ - k₁).natAbs : ℝ)) ^ muPi <
      ε / ((k₂ - k₁).natAbs : ℝ) := by
  have hk_diff : k₂ - k₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hk)
  suffices ∃ p : ℤ, (↑p : ℝ) / (2 * ((k₂ - k₁).natAbs : ℝ)) =
      (↑n₂ - ↑n₁) / (2 * (↑k₂ - ↑k₁)) by
    obtain ⟨p, hp⟩ := this
    have step1 := hPi p (2 * (k₂ - k₁).natAbs)
      (Nat.mul_pos (by norm_num) (Int.natAbs_pos.mpr hk_diff)) hQ
    rw [show (↑(2 * (k₂ - k₁).natAbs) : ℝ) = 2 * ((k₂ - k₁).natAbs : ℝ) from by
        push_cast
        ring,
      hp] at step1
    exact lt_trans step1 happrox
  rcases Int.lt_or_lt_of_ne hk_diff with h | h
  · exact ⟨n₁ - n₂, by
      rw [show ((k₂ - k₁).natAbs : ℝ) = -(↑k₂ - ↑k₁) from by
        rw [Nat.cast_natAbs, abs_of_neg h, Int.cast_neg, Int.cast_sub]]
      have : (↑(n₁ - n₂) : ℝ) = -(↑n₂ - ↑n₁) := by
        push_cast
        ring
      rw [this, mul_neg, neg_div_neg_eq]⟩
  · exact ⟨n₂ - n₁, by
      rw [show ((k₂ - k₁).natAbs : ℝ) = ↑k₂ - ↑k₁ from by
        rw [Nat.cast_natAbs, abs_of_pos h, Int.cast_sub]]
      congr 1
      exact Int.cast_sub n₂ n₁⟩

lemma gap_principle_of_PiIrrBound (hpi : PiIrrBound) :
    ∃ (C_gap : ℝ) (Q₀ : ℕ), 0 < C_gap ∧
    ∀ (n₁ n₂ : ℤ) (k₁ k₂ : ℤ) (ε : ℝ),
      0 < ε → ε < 1 →
      k₁ ≠ k₂ →
      Q₀ ≤ 2 * (k₂ - k₁).natAbs →
      |↑n₁ - (Real.pi / 2 + 2 * Real.pi * ↑k₁)| < ε →
      |↑n₂ - (Real.pi / 2 + 2 * Real.pi * ↑k₂)| < ε →
      C_gap * ε ^ (-(1 : ℝ) / (muPi - 1)) ≤ |(k₂ - k₁ : ℤ)| := by
  obtain ⟨C, Q₀, hC, hPi⟩ := hpi
  refine ⟨(C / ((2 : ℝ) ^ muPi)) ^ ((1 : ℝ) / (muPi - 1)), Q₀,
    Real.rpow_pos_of_pos (div_pos hC (by positivity)) _, ?_⟩
  intro n₁ n₂ k₁ k₂ ε hε _hε1 hk hQ h1 h2
  rw [C_gap_epsilon_eq C ε hC hε]
  convert gap_bound_from_irrationality C ε ((k₂ - k₁).natAbs : ℝ) hC hε
    (by exact_mod_cast Int.natAbs_pos.mpr (sub_ne_zero.mpr (Ne.symm hk)))
    (apply_PiIrrBound_to_approx C Q₀ hPi n₁ n₂ k₁ k₂ ε hk hQ
      (pi_rational_approx_bound n₁ n₂ k₁ k₂ ε hk h1 h2)) using 1
  simp only [Int.abs_eq_natAbs]
  exact Int.cast_natCast _

/-! ## Bad part summability via irrationality measure of π -/

private noncomputable def badTerm (n : ℕ) : ℝ :=
  if hn : 0 < n then
    if ¬good ⟨n, hn⟩ then (1 : ℝ) / (n : ℝ) else 0
  else 0

private lemma badTerm_nonneg (n : ℕ) : 0 ≤ badTerm n := by
  unfold badTerm
  split_ifs <;> positivity

private lemma k_of_abs_le_of_mem_block (j : ℕ) (n : ℕ) (hn_mem : n ∈ Finset.Ico (2^j) (2^(j+1))) :
    |k_of (↑n : ℝ)| ≤ 2^(j+1) := by
  have hn_lt := (Finset.mem_Ico.mp hn_mem).2
  have hy_mem := y_of_mem_Icc (↑n : ℝ)
  have hpi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have habs_2pi_k : |2 * Real.pi * (k_of (↑n : ℝ))| ≤ ↑n + 3 * Real.pi / 2 := by
    rw [show 2 * Real.pi * (k_of (↑n : ℝ)) = ↑n - Real.pi / 2 - y_of (↑n : ℝ) from by
      linarith [y_of_spec (↑n : ℝ)], abs_le]
    exact ⟨by linarith [Real.pi_pos, hy_mem.2], by linarith [hy_mem.1]⟩
  have hn_lt_real : (↑n : ℝ) < (↑(2^(j+1) : ℕ) : ℝ) := Nat.cast_lt.mpr hn_lt
  have h_coeff : 3 * Real.pi / 2 ≤ (2 * Real.pi - 1) * ↑(2^(j+1) : ℕ) := by
    have : (2 : ℝ) ≤ ↑(2^(j+1) : ℕ) := by exact_mod_cast show 2 ≤ 2^(j+1) by rw [pow_succ]; omega
    nlinarith [Real.pi_gt_three]
  have h_k_lt : |(↑(k_of (↑n : ℝ)) : ℝ)| < (↑(2^(j+1) : ℕ) : ℝ) := by
    have : |2 * Real.pi * ↑(k_of (↑n : ℝ))| < 2 * Real.pi * ↑(2^(j+1) : ℕ) := by linarith
    rw [abs_mul, abs_of_pos hpi_pos] at this
    exact lt_of_mul_lt_mul_left this hpi_pos.le
  exact_mod_cast h_k_lt.le

private lemma residue_class_gap (T : Finset ℤ) (D : ℝ) (Q₀ : ℕ) (r : ZMod (Q₀ + 1))
    (hT_gap : ∀ k₁ ∈ T, ∀ k₂ ∈ T, k₁ ≠ k₂ → (Q₀ : ℤ) ≤ 2 * (k₂ - k₁).natAbs →
      D ≤ |(k₂ - k₁ : ℤ)|)
    (k₁ : ℤ) (hk₁ : k₁ ∈ T.filter (fun k : ℤ => (k : ZMod (Q₀ + 1)) = r))
    (k₂ : ℤ) (hk₂ : k₂ ∈ T.filter (fun k : ℤ => (k : ZMod (Q₀ + 1)) = r))
    (hne : k₁ ≠ k₂) :
    D ≤ |(k₂ - k₁ : ℤ)| := by
  exact hT_gap k₁ (Finset.mem_filter.mp hk₁).1 k₂ (Finset.mem_filter.mp hk₂).1 hne (by
    have h1 := Int.natAbs_dvd_natAbs.mpr (show (↑(Q₀ + 1) : ℤ) ∣ (k₂ - k₁) by
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub,
        (Finset.mem_filter.mp hk₁).2, (Finset.mem_filter.mp hk₂).2])
    rw [Int.natAbs_natCast] at h1
    have h2 := Nat.le_of_dvd (Int.natAbs_pos.mpr (sub_ne_zero.mpr (Ne.symm hne))) h1
    omega)

private lemma card_le_of_pairwise_gap (S : Finset ℤ) (B D : ℝ)
    (hD_pos : 0 < D)
    (hB_nonneg : 0 ≤ B)
    (hS_range : ∀ k ∈ S, (|k| : ℝ) ≤ B)
    (hS_gap : ∀ k₁ ∈ S, ∀ k₂ ∈ S, k₁ ≠ k₂ → D ≤ |(k₂ - k₁ : ℤ)|) :
    (S.card : ℝ) ≤ 2 * B / D + 1 := by
  by_cases hcard : S.card ≤ 1
  · linarith [show (S.card : ℝ) ≤ 1 from by exact_mod_cast hcard,
      div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hB_nonneg) (le_of_lt hD_pos)]
  · push_neg at hcard
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    have hmin_mem := Finset.min'_mem S hne
    have hmax_mem := Finset.max'_mem S hne
    have hspan : (S.max' hne : ℝ) - (S.min' hne : ℝ) ≤ 2 * B := by
      linarith [(abs_le.mp (hS_range _ hmin_mem)).1, (abs_le.mp (hS_range _ hmax_mem)).2]
    have hgap_ne : S.min' hne ≠ S.max' hne := by
      intro heq
      have h1 : ∀ x ∈ S, x = S.min' hne := fun x hx =>
        le_antisymm (heq ▸ Finset.le_max' S x hx) (Finset.min'_le S x hx)
      exact absurd (Finset.card_le_one.mpr (fun a ha b hb => by rw [h1 a ha, h1 b hb])) (by omega)
    have hgap_max_min := hS_gap _ hmin_mem _ hmax_mem hgap_ne
    rw [abs_of_nonneg (sub_nonneg.mpr (Finset.min'_le_max' S hne))] at hgap_max_min
    set L := S.sort (· ≤ ·) with _
    have hL_len : L.length = S.card := Finset.length_sort _
    have hL_sorted := S.sortedLT_sort
    have hL_mem : ∀ x, x ∈ L ↔ x ∈ S := fun x => Finset.mem_sort _
    have hlen_pos : 0 < L.length := by omega
    have hfirst : L[0]'(by omega) = S.min' hne :=
      Finset.min'_eq_sorted_zero.symm
    have hlast : L[L.length - 1]'(by omega) = S.max' hne :=
      Finset.max'_eq_sorted_last.symm
    have hconsec : ∀ i (hi : i < L.length - 1),
        D ≤ ↑(L[i + 1]'(by omega) - L[i]'(by omega)) := by
      intro i hi
      have hlt : L[i]'(by omega) < L[i + 1]'(by omega) := by
        have := hL_sorted (show (⟨i, by omega⟩ : Fin L.length) < ⟨i + 1, by omega⟩ from by
          simp [Fin.lt_def])
        simpa [List.get_eq_getElem] using this
      have hgap := hS_gap _ ((hL_mem _).mp (List.getElem_mem (by omega)))
        _ ((hL_mem _).mp (List.getElem_mem (by omega))) (ne_of_lt hlt)
      rwa [abs_of_nonneg (show (0 : ℤ) ≤ L[i + 1]'(by omega) - L[i]'(by omega) by omega)] at hgap
    suffices htel : (S.card - 1 : ℝ) * D ≤ ↑(S.max' hne - S.min' hne) by
      have : (S.card : ℝ) - 1 ≤ 2 * B / D := by
        rw [le_div_iff₀ hD_pos]
        calc (S.card - 1 : ℝ) * D ≤ ↑(S.max' hne - S.min' hne) := htel
          _ = (S.max' hne : ℝ) - (S.min' hne : ℝ) := by
            push_cast
            ring
          _ ≤ 2 * B := hspan
      linarith
    have hind : ∀ n (hn : n < L.length), (n : ℝ) * D ≤ ↑(L[n]'hn - L[0]'hlen_pos) := by
      intro n hn
      induction n with
      | zero => simp
      | succ k ih =>
        rw [show ((k + 1 : ℕ) : ℝ) * D = (k : ℝ) * D + D by
            push_cast
            ring,
          show (L[k + 1]'hn - L[0]'hlen_pos : ℤ) =
            (L[k]'(by omega) - L[0]'hlen_pos) + (L[k + 1]'hn - L[k]'(by omega)) from by ring,
          Int.cast_add]
        linarith [ih (by omega), hconsec k (by omega)]
    have h_final := hind (L.length - 1) (by omega)
    rw [hlast, hfirst] at h_final
    rwa [show (S.card - 1 : ℝ) = ((L.length - 1 : ℕ) : ℝ) from by
      simp [Nat.cast_sub (show 1 ≤ S.card by omega), hL_len]]

private lemma residue_class_card_le (T : Finset ℤ) (B D : ℝ) (Q₀ : ℕ) (r : ZMod (Q₀ + 1))
    (hD_pos : 0 < D)
    (hB_nonneg : 0 ≤ B)
    (hT_range : ∀ k ∈ T, (|k| : ℝ) ≤ B)
    (hT_gap : ∀ k₁ ∈ T, ∀ k₂ ∈ T, k₁ ≠ k₂ → (Q₀ : ℤ) ≤ 2 * (k₂ - k₁).natAbs →
      D ≤ |(k₂ - k₁ : ℤ)|) :
    ((T.filter (fun (k : ℤ) => (k : ZMod (Q₀ + 1)) = r)).card : ℝ) ≤ 2 * B / D + 1 :=
  card_le_of_pairwise_gap _ B D hD_pos hB_nonneg
    (fun k hk => hT_range k (Finset.mem_filter.mp hk).1)
    (fun k₁ hk₁ k₂ hk₂ hne => residue_class_gap T D Q₀ r hT_gap k₁ hk₁ k₂ hk₂ hne)

private lemma integer_clustering_bound
    (K : Finset ℤ) (R : ℝ) (Q₀ : ℕ) (Δ : ℝ)
    (hR_pos : 0 < R) (hΔ_pos : 0 < Δ)
    (hK_range : ∀ k ∈ K, (|k| : ℝ) ≤ R)
    (hK_gap : ∀ k₁ ∈ K, ∀ k₂ ∈ K, k₁ ≠ k₂ →
      Q₀ ≤ 2 * (k₂ - k₁).natAbs → Δ ≤ |(k₂ - k₁ : ℤ)|) :
    (K.card : ℝ) ≤ (↑Q₀ + 1) * (2 * R / Δ + 1) := by
  by_cases hT : K.Nonempty
  · obtain ⟨k, hk⟩ := hT
    rw [show (K.card : ℝ) =
        ∑ r : ZMod (Q₀ + 1), ((K.filter (fun (k : ℤ) => (k : ZMod (Q₀ + 1)) = r)).card : ℝ) from by
      have h := @Finset.card_eq_sum_card_fiberwise _ (ZMod (Q₀ + 1)) _
        (fun (k : ℤ) => (k : ZMod (Q₀ + 1))) K Finset.univ
        (fun _ _ => Finset.mem_univ (α := ZMod (Q₀ + 1)) _)
      simp at h
      push_cast [h]
      ring_nf]
    calc ∑ r : ZMod (Q₀ + 1), ((K.filter (fun (k : ℤ) => (k : ZMod (Q₀ + 1)) = r)).card : ℝ)
        ≤ ∑ _r : ZMod (Q₀ + 1), (2 * R / Δ + 1) :=
          Finset.sum_le_sum (fun r _ => residue_class_card_le K R Δ Q₀ r hΔ_pos
            (le_trans (abs_nonneg (k : ℝ)) (hK_range k hk)) hK_range
            (fun k₁ hk₁ k₂ hk₂ hne hQ => hK_gap k₁ hk₁ k₂ hk₂ hne (by exact_mod_cast hQ)))
      _ = (↑Q₀ + 1) * (2 * R / Δ + 1) := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card]
          simp
          ring
  · simp [Finset.not_nonempty_iff_eq_empty.mp hT]
    positivity

private lemma k_image_gap_constraint
    (C_gap : ℝ) (Q₀_gap : ℕ) (_hC_gap : 0 < C_gap)
    (hgap : ∀ (n₁ n₂ : ℤ) (k₁ k₂ : ℤ) (ε : ℝ),
      0 < ε → ε < 1 →
      k₁ ≠ k₂ →
      Q₀_gap ≤ 2 * (k₂ - k₁).natAbs →
      |↑n₁ - (Real.pi / 2 + 2 * Real.pi * ↑k₁)| < ε →
      |↑n₂ - (Real.pi / 2 + 2 * Real.pi * ↑k₂)| < ε →
      C_gap * ε ^ (-(1 : ℝ) / (muPi - 1)) ≤ |(k₂ - k₁ : ℤ)|)
    (j : ℕ) (hj : 5 ≤ j) (S : Finset ℕ)
    (hS_sub : S ⊆ Finset.Ico (2^j) (2^(j+1)))
    (hS_bad : ∀ n ∈ S, ∀ (hn_pos : 0 < n), ¬good ⟨n, hn_pos⟩)
    (hS_pos : ∀ n ∈ S, 0 < n)
    (K : Finset ℤ) (hK_def : K = S.image (fun (n : ℕ) => k_of (↑n : ℝ))) :
    ∀ k₁ ∈ K, ∀ k₂ ∈ K, k₁ ≠ k₂ →
      Q₀_gap ≤ 2 * (k₂ - k₁).natAbs →
      C_gap * (((2 : ℝ)^j) ^ (-(1/4 : ℝ))) ^ (-(1 : ℝ) / (muPi - 1)) ≤ |(k₂ - k₁ : ℤ)| := by
  intro k₁ hk₁ k₂ hk₂ hk_ne hQ
  rw [hK_def] at hk₁ hk₂
  simp only [Finset.mem_image] at hk₁ hk₂
  obtain ⟨n₁, hn₁_mem, hk₁_eq⟩ := hk₁
  obtain ⟨n₂, hn₂_mem, hk₂_eq⟩ := hk₂
  rw [← hk₁_eq, ← hk₂_eq] at hk_ne hQ ⊢
  have hclose : ∀ m ∈ S, ∀ hmp : 0 < m, ¬good ⟨m, hmp⟩ → m ∈ Finset.Ico (2^j) (2^(j+1)) →
      |((m : ℤ) : ℝ) - (Real.pi / 2 + 2 * Real.pi * ↑(k_of (↑m : ℝ)))| <
        ((2 : ℝ)^j) ^ (-(1/4 : ℝ)) := by
    intro m _ hmp hbad hmblock
    rw [Int.cast_natCast, show (↑m : ℝ) - (Real.pi / 2 + 2 * Real.pi * ↑(k_of (↑m : ℝ))) =
      y_of ↑m by
        simp only [y_of, k_of]
        ring]
    exact lt_of_lt_of_le (not_le.mp hbad) (Real.rpow_le_rpow_of_nonpos (by positivity)
      (by exact_mod_cast (Finset.mem_Ico.mp hmblock).1) (by norm_num))
  exact hgap (n₁ : ℤ) (n₂ : ℤ) (k_of (↑n₁ : ℝ)) (k_of (↑n₂ : ℝ)) (((2 : ℝ)^j) ^ (-(1/4 : ℝ)))
    (Real.rpow_pos_of_pos (by positivity) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast Nat.one_lt_two_pow_iff.mpr (by omega))
      (by norm_num))
    hk_ne hQ
    (hclose n₁ hn₁_mem (hS_pos n₁ hn₁_mem) (hS_bad n₁ hn₁_mem (hS_pos n₁ hn₁_mem)) (hS_sub hn₁_mem))
    (hclose n₂ hn₂_mem (hS_pos n₂ hn₂_mem) (hS_bad n₂ hn₂_mem (hS_pos n₂ hn₂_mem)) (hS_sub hn₂_mem))

private lemma rpow_neg_quarter_lt_half {n : ℝ} (hn : 32 ≤ n) :
    n ^ (-(1/4 : ℝ)) < 1/2 := by
  linarith [Real.rpow_lt_rpow_of_neg (by norm_num : (0:ℝ) < 16) (by linarith : (16 : ℝ) < n)
    (by norm_num : -(1/4 : ℝ) < 0)]

private lemma k_of_injOn_S
    (j : ℕ) (hj : 5 ≤ j) (S : Finset ℕ)
    (hS_sub : S ⊆ Finset.Ico (2^j) (2^(j+1)))
    (hS_bad : ∀ n ∈ S, ∀ (hn_pos : 0 < n), ¬good ⟨n, hn_pos⟩)
    (hS_pos : ∀ n ∈ S, 0 < n) :
    Set.InjOn (fun (n : ℕ) => k_of (↑n : ℝ)) (↑S : Set ℕ) := by
  intro m hm n hn hk_eq
  simp only [Finset.mem_coe] at hm hn
  change k_of (↑m : ℝ) = k_of (↑n : ℝ) at hk_eq
  by_contra hne
  have hj5 : (32 : ℕ) ≤ 2^j := le_trans (show (32 : ℕ) ≤ 2^5 by norm_num) (Nat.pow_le_pow_right (by norm_num) hj)
  have h_lt_1 : |(↑m : ℝ) - ↑n| < 1 := by
    rw [show (↑m : ℝ) - ↑n = y_of ↑m - y_of ↑n by
      have := y_of_spec (↑m : ℝ)
      rw [hk_eq] at this
      linarith [y_of_spec (↑n : ℝ)]]
    linarith [show |y_of ↑m - y_of ↑n| ≤ |y_of ↑m| + |y_of ↑n| by grind,
      show |y_of (↑m : ℝ)| < 1/2 from lt_trans (not_le.mp (hS_bad m hm (hS_pos m hm)))
        (rpow_neg_quarter_lt_half (show (32 : ℝ) ≤ ↑m by exact_mod_cast le_trans hj5 (Finset.mem_Ico.mp (hS_sub hm)).1)),
      show |y_of (↑n : ℝ)| < 1/2 from lt_trans (not_le.mp (hS_bad n hn (hS_pos n hn)))
        (rpow_neg_quarter_lt_half (show (32 : ℝ) ≤ ↑n by exact_mod_cast le_trans hj5 (Finset.mem_Ico.mp (hS_sub hn)).1))]
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · linarith [neg_abs_le ((↑m : ℝ) - ↑n), show (↑m + 1 : ℝ) ≤ ↑n from by exact_mod_cast h]
  · linarith [le_abs_self ((↑m : ℝ) - ↑n), show (↑n + 1 : ℝ) ≤ ↑m from by exact_mod_cast h]

private lemma bad_count_in_block_core
    (C_gap : ℝ) (Q₀_gap : ℕ) (hC_gap : 0 < C_gap)
    (hgap : ∀ (n₁ n₂ : ℤ) (k₁ k₂ : ℤ) (ε : ℝ),
      0 < ε → ε < 1 →
      k₁ ≠ k₂ →
      Q₀_gap ≤ 2 * (k₂ - k₁).natAbs →
      |↑n₁ - (Real.pi / 2 + 2 * Real.pi * ↑k₁)| < ε →
      |↑n₂ - (Real.pi / 2 + 2 * Real.pi * ↑k₂)| < ε →
      C_gap * ε ^ (-(1 : ℝ) / (muPi - 1)) ≤ |(k₂ - k₁ : ℤ)|)
    (j : ℕ) (hj : 5 ≤ j) (S : Finset ℕ)
    (hS_sub : S ⊆ Finset.Ico (2^j) (2^(j+1)))
    (hS_bad : ∀ n ∈ S, ∀ (hn_pos : 0 < n), ¬good ⟨n, hn_pos⟩)
    (hS_pos : ∀ n ∈ S, 0 < n) :
      S.card ≤
      ⌈(↑Q₀_gap + 1 : ℝ) * ((2 : ℝ)^(j+2) / (C_gap * ((2 : ℝ)^j) ^ ((1 : ℝ)/(4 * (muPi - 1)))) + 1)⌉₊ := by
  set K := S.image (fun (n : ℕ) => k_of (↑n : ℝ)) with hK_def
  set Δ := C_gap * (((2 : ℝ)^j) ^ (-(1/4 : ℝ))) ^ (-(1 : ℝ) / (muPi - 1)) with hΔ_def
  have hcluster := integer_clustering_bound K ((2 : ℝ)^(j+1)) Q₀_gap Δ
    (by positivity) (mul_pos hC_gap
      (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by positivity) _) _))
    (fun k hk => by
      rw [hK_def, Finset.mem_image] at hk
      obtain ⟨n, hn_mem, rfl⟩ := hk
      exact_mod_cast k_of_abs_le_of_mem_block j n (hS_sub hn_mem))
    (k_image_gap_constraint C_gap Q₀_gap hC_gap hgap j hj S hS_sub hS_bad hS_pos K hK_def)
  have hrpow_eq : ∀ (C : ℝ) (j : ℕ),
      C * (((2 : ℝ)^j) ^ (-(1/4 : ℝ))) ^ (-(1 : ℝ) / (muPi - 1)) =
      C * ((2 : ℝ)^j) ^ ((1 : ℝ)/(4 * (muPi - 1))) := fun C j => by
    congr 1
    rw [← Real.rpow_mul (by positivity)]
    norm_num [show muPi = (710321 : ℝ) / 100000 by norm_num]
  rw [hΔ_def, hrpow_eq, show 2 * (2 : ℝ)^(j+1) = (2 : ℝ)^(j+2) from by ring] at hcluster
  rw [(Finset.card_image_of_injOn (k_of_injOn_S j hj S hS_sub hS_bad hS_pos)).symm]
  calc K.card = ⌈(↑K.card : ℝ)⌉₊ := (Nat.ceil_natCast K.card).symm
    _ ≤ _ := Nat.ceil_le_ceil hcluster

private lemma bound_conversion (C_gap : ℝ) (Q₀_gap : ℕ) (hC_gap : 0 < C_gap) :
    ∃ (A : ℝ) (j₁ : ℕ), 0 < A ∧ ∀ j : ℕ, j₁ ≤ j →
      (⌈(↑Q₀_gap + 1 : ℝ) * ((2 : ℝ)^(j+2) / (C_gap * ((2 : ℝ)^j) ^ ((1 : ℝ)/(4 * (muPi - 1)))) + 1)⌉₊ : ℝ) ≤
      A * ((2 : ℝ)^j) ^ (1 - (1 : ℝ)/(4 * (muPi - 1))) := by
  set γ := (1 : ℝ)/(4 * (muPi - 1))
  refine ⟨(↑Q₀_gap + 1) * (4 / C_gap) + ↑Q₀_gap + 2, 0, ?_, ?_⟩
  · positivity
  · intro j _
    have hrpow : (2 : ℝ)^(j+2) / ((2 : ℝ)^j) ^ γ = 4 * ((2 : ℝ)^j) ^ (1 - γ) := by
      rw [show (2 : ℝ)^(j+2) = 4 * (2 : ℝ)^j from by ring, mul_div_assoc]
      congr 1
      rw [Real.rpow_sub (pow_pos (by norm_num : (0:ℝ) < 2) j) 1, Real.rpow_one]
    set x := (↑Q₀_gap + 1 : ℝ) * ((2 : ℝ)^(j+2) / (C_gap * ((2 : ℝ)^j) ^ γ) + 1)
    have hx : (0 : ℝ) ≤ x := by positivity
    have hceil : (⌈x⌉₊ : ℝ) ≤ x + 1 := by
      have h1 : (⌈x⌉₊ : ℝ) ≤ ↑(⌊x⌋₊ + 1) := by exact_mod_cast Nat.ceil_le_floor_add_one x
      linarith [Nat.floor_le hx, show (⌊x⌋₊ + 1 : ℕ) = (⌊x⌋₊ : ℝ) + 1 from by
          push_cast
          ring]
    have h1le : 1 ≤ ((2 : ℝ)^j) ^ (1 - γ) :=
      Real.one_le_rpow (by exact_mod_cast Nat.one_le_two_pow) (by norm_num)
    calc (⌈(↑Q₀_gap + 1 : ℝ) * ((2 : ℝ)^(j+2) / (C_gap * ((2 : ℝ)^j) ^ γ) + 1)⌉₊ : ℝ)
        ≤ (↑Q₀_gap + 1) * ((2 : ℝ)^(j+2) / (C_gap * ((2 : ℝ)^j) ^ γ) + 1) + 1 := hceil
      _ = (↑Q₀_gap + 1) * (4 / C_gap) * ((2 : ℝ)^j) ^ (1 - γ) + (↑Q₀_gap + 1) + 1 := by
          rw [show (2 : ℝ)^(j+2) / (C_gap * ((2 : ℝ)^j) ^ γ) =
            ((2 : ℝ)^(j+2) / ((2 : ℝ)^j) ^ γ) / C_gap from by
              rw [div_div]
              ring_nf, hrpow]
          ring
      _ ≤ ((↑Q₀_gap + 1) * (4 / C_gap) + ↑Q₀_gap + 2) * ((2 : ℝ)^j) ^ (1 - γ) := by
          set r := ((2 : ℝ)^j) ^ (1 - γ)
          linarith [le_mul_of_one_le_right (show (0 : ℝ) ≤ ↑Q₀_gap + 2 by positivity) h1le]

private lemma bad_count_in_block_assembled (hpi : PiIrrBound) :
    ∃ (A : ℝ) (j₀ : ℕ), 0 < A ∧
    ∀ j : ℕ, j₀ ≤ j →
    ∀ (S : Finset ℕ),
      S ⊆ Finset.Ico (2^j) (2^(j+1)) →
      (∀ n ∈ S, ∀ (hn_pos : 0 < n), ¬good ⟨n, hn_pos⟩) →
      (∀ n ∈ S, 0 < n) →
      (S.card : ℝ) ≤ A * ((2 : ℝ)^j) ^ (1 - (1 : ℝ)/(4 * (muPi - 1))) := by
  obtain ⟨C_gap, Q₀, hC_gap, hgap⟩ := gap_principle_of_PiIrrBound hpi
  obtain ⟨A, j₁, hA, hconv⟩ := bound_conversion C_gap Q₀ hC_gap
  refine ⟨A, max 5 j₁, hA, ?_⟩
  intro j hj S hS_sub hS_bad hS_pos
  exact le_trans
    (by exact_mod_cast bad_count_in_block_core C_gap Q₀ hC_gap hgap j (by omega) S hS_sub hS_bad hS_pos)
    (hconv j (by omega))

private lemma bad_count_in_block (hpi : PiIrrBound) :
    ∃ (A : ℝ) (j₀ : ℕ), 0 < A ∧
    ∀ j : ℕ, j₀ ≤ j →
      ((Finset.Ico (2^j) (2^(j+1))).filter (fun n =>
        match (inferInstance : Decidable (0 < n)) with
        | .isTrue h => ¬good ⟨n, h⟩
        | .isFalse _ => False)).card ≤
      A * ((2 : ℝ)^j) ^ (1 - (1 : ℝ)/(4 * (muPi - 1))) := by
  obtain ⟨A, j₀, hA, hassembled⟩ := bad_count_in_block_assembled hpi
  refine ⟨A, j₀, hA, fun j hj => ?_⟩
  set S := (Finset.Ico (2^j) (2^(j+1))).filter (fun n =>
    match (inferInstance : Decidable (0 < n)) with
    | .isTrue h => ¬good ⟨n, h⟩
    | .isFalse _ => False) with hS_def
  have hS_sub : S ⊆ Finset.Ico (2^j) (2^(j+1)) := Finset.filter_subset _ _
  have hS_pos : ∀ n ∈ S, 0 < n := fun n hn =>
    lt_of_lt_of_le (Nat.two_pow_pos j) (Finset.mem_Ico.mp (hS_sub hn)).1
  have hS_bad : ∀ n ∈ S, ∀ (hn_pos : 0 < n), ¬good ⟨n, hn_pos⟩ := by
    intro n hn hn_pos
    simp only [hS_def, Finset.mem_filter] at hn
    obtain ⟨_, hprop⟩ := hn
    revert hprop
    cases (inferInstance : Decidable (0 < n)) with
    | isTrue h => exact id
    | isFalse h => exact absurd hn_pos h
  exact_mod_cast hassembled j hj S hS_sub hS_bad hS_pos

private lemma badTerm_le_inv_pow (j : ℕ) (n : ℕ) (hn : n ∈ Finset.Ico (2^j) (2^(j+1))) :
    badTerm n ≤ 1 / ((2 : ℝ)^j) := by
  simp only [badTerm]
  split_ifs with h1 h2
  all_goals (first
    | exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (Finset.mem_Ico.mp hn).1)
    | exact div_nonneg (by norm_num) (pow_nonneg (by norm_num) j))

private lemma block_sum_le_card_div (j : ℕ) :
    ∑ n ∈ (Finset.Ico (2^j) (2^(j+1))), badTerm n ≤
      ((Finset.Ico (2^j) (2^(j+1))).filter (fun n =>
        match (inferInstance : Decidable (0 < n)) with
        | .isTrue h => ¬good ⟨n, h⟩
        | .isFalse _ => False)).card * (1 / ((2 : ℝ)^j)) := by
  have heq : ∑ n ∈ (Finset.Ico (2^j) (2^(j+1))), badTerm n =
      ∑ n ∈ (Finset.Ico (2^j) (2^(j+1))).filter (fun n =>
        match (inferInstance : Decidable (0 < n)) with
        | .isTrue h => ¬good ⟨n, h⟩
        | .isFalse _ => False), badTerm n := by
    symm
    apply Finset.sum_filter_of_ne
    intro x _ hbad
    have ⟨hpos, hng⟩ : ∃ (hpos : 0 < x), ¬good ⟨x, hpos⟩ := by
      simp only [badTerm] at hbad
      split_ifs at hbad with h1 h2
      · exact absurd rfl hbad
      · exact ⟨h1, h2⟩
      · exact absurd rfl hbad
    exact match h : (inferInstance : Decidable (0 < x)) with
    | .isTrue _ => hng
    | .isFalse h' => absurd hpos h'
  rw [heq]
  calc ∑ n ∈ _, badTerm n
      ≤ _ • (1 / ((2 : ℝ)^j)) :=
        Finset.sum_le_card_nsmul _ _ _ (fun x hx =>
          badTerm_le_inv_pow j x (Finset.filter_subset _ _ hx))
    _ = _ * (1 / ((2 : ℝ)^j)) := by rw [nsmul_eq_mul]

private lemma dyadic_block_bound (hpi : PiIrrBound) :
    ∃ (K : ℝ) (r : ℝ) (j₀ : ℕ), 0 < K ∧ 0 ≤ r ∧ r < 1 ∧
    ∀ j : ℕ, j₀ ≤ j →
      ∑ n ∈ (Finset.Ico (2^j) (2^(j+1))), badTerm n ≤ K * r ^ j := by
  obtain ⟨A, j₀, hA, hcount⟩ := bad_count_in_block hpi
  refine ⟨A, (2 : ℝ) ^ (-(1 : ℝ)/(4 * (muPi - 1))), j₀,
    hA, le_of_lt (Real.rpow_pos_of_pos (by norm_num) _),
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num [div_eq_mul_inv]), ?_⟩
  intro j hj
  calc ∑ n ∈ (Finset.Ico (2^j) (2^(j+1))), badTerm n
      ≤ ((Finset.Ico (2^j) (2^(j+1))).filter (fun n =>
          match (inferInstance : Decidable (0 < n)) with
          | .isTrue h => ¬good ⟨n, h⟩
          | .isFalse _ => False)).card * (1 / ((2 : ℝ)^j)) :=
        block_sum_le_card_div j
    _ ≤ A * ((2 : ℝ)^j) ^ (1 - (1 : ℝ)/(4 * (muPi - 1))) * (1 / ((2 : ℝ)^j)) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hcount j hj
        · positivity
    _ = A * ((2 : ℝ) ^ (-(1 : ℝ)/(4 * (muPi - 1)))) ^ j := by
        rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2),
          show (1 : ℝ) / (2 : ℝ) ^ j = ((2 : ℝ)⁻¹) ^ j from by rw [one_div, inv_pow],
          mul_assoc, ← mul_pow, ← Real.rpow_neg_one (2 : ℝ),
          ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        congr 1
        ring_nf

private lemma Ico_one_subset_biUnion_dyadic (N : ℕ) :
    Finset.Ico 1 N ⊆ (Finset.range (Nat.log 2 N + 1)).biUnion
      (fun j => Finset.Ico (2^j) (2^(j+1))) := by
  intro n hn
  simp only [Finset.mem_Ico] at hn
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_Ico]
  exact ⟨Nat.log 2 n, Nat.lt_succ_of_le (Nat.log_mono_right (le_of_lt hn.2)),
    Nat.pow_log_le_self 2 (by omega), Nat.lt_pow_succ_log_self (by norm_num) n⟩

private lemma pairwiseDisjoint_dyadic_blocks (S : Finset ℕ) :
    Set.PairwiseDisjoint (↑S)
      (fun j => Finset.Ico (2^j) (2^(j+1))) := by
  intro i _ j _ hij
  simp only [Function.onFun, Finset.disjoint_left, Finset.mem_Ico]
  intro n ⟨hn1, hn2⟩ ⟨hn3, _⟩
  rcases Nat.lt_or_gt_of_ne hij with h | h <;>
  · have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h
    omega

private lemma partial_sum_le_block_sums (N : ℕ) :
    ∑ n ∈ Finset.range N, badTerm n ≤
    ∑ j ∈ Finset.range (Nat.log 2 N + 1),
      ∑ n ∈ Finset.Ico (2^j) (2^(j+1)), badTerm n := by
  rw [← Finset.sum_biUnion (pairwiseDisjoint_dyadic_blocks _),
    show ∑ n ∈ Finset.range N, badTerm n = ∑ n ∈ Finset.Ico 1 N, badTerm n from by
      rcases N.eq_zero_or_pos with rfl | hN
      · simp
      · rw [Finset.range_eq_Ico,
          ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le 1) hN,
          Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive 0 1 N)]
        simp [show badTerm 0 = 0 by simp [badTerm]]]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Ico_one_subset_biUnion_dyadic N)
    (fun i _ _ => badTerm_nonneg i)

private lemma block_sum_le_one (j : ℕ) :
    ∑ n ∈ Finset.Ico (2^j) (2^(j+1)), badTerm n ≤ 1 := by
  calc ∑ n ∈ Finset.Ico (2^j) (2^(j+1)), badTerm n
      ≤ (Finset.Ico (2^j) (2^(j+1))).card • (1 / ((2 : ℝ)^j)) :=
        Finset.sum_le_card_nsmul _ _ _ (fun n hn => badTerm_le_inv_pow j n hn)
    _ = 1 := by
        simp [nsmul_eq_mul, show 2 ^ (j + 1) - 2 ^ j = 2 ^ j from by
            rw [pow_succ]
            omega,
          Nat.cast_pow, Nat.cast_ofNat]

private lemma early_blocks_bound (j₀ : ℕ) (J : ℕ) :
    ∑ j ∈ Finset.range (min J j₀), ∑ n ∈ Finset.Ico (2^j) (2^(j+1)), badTerm n ≤ ↑j₀ := by
  calc ∑ j ∈ Finset.range (min J j₀), ∑ n ∈ Finset.Ico (2^j) (2^(j+1)), badTerm n
      ≤ ∑ _j ∈ Finset.range (min J j₀), (1 : ℝ) :=
        Finset.sum_le_sum (fun j _ => block_sum_le_one j)
    _ ≤ ↑j₀ := by simp

private lemma late_blocks_bound (K r : ℝ) (j₀ : ℕ) (hK : 0 < K) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hblock : ∀ j : ℕ, j₀ ≤ j → ∑ n ∈ Finset.Ico (2^j) (2^(j+1)), badTerm n ≤ K * r ^ j)
    (J : ℕ) :
    ∑ j ∈ Finset.Ico j₀ J, ∑ n ∈ Finset.Ico (2^j) (2^(j+1)), badTerm n ≤ K * (1 - r)⁻¹ := by
  calc ∑ j ∈ Finset.Ico j₀ J, ∑ n ∈ Finset.Ico (2^j) (2^(j+1)), badTerm n
      ≤ ∑ j ∈ Finset.Ico j₀ J, (K * r ^ j) :=
        Finset.sum_le_sum (fun j hj => hblock j (Finset.mem_Ico.mp hj).1)
    _ = K * ∑ j ∈ Finset.Ico j₀ J, r ^ j := by rw [Finset.mul_sum]
    _ ≤ K * ∑' j, r ^ j := mul_le_mul_of_nonneg_left
        ((summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ (fun i _ => pow_nonneg hr0 i)) hK.le
    _ = K * (1 - r)⁻¹ := by rw [tsum_geometric_of_lt_one hr0 hr1]

private lemma block_sums_uniformly_bounded (hpi : PiIrrBound) :
    ∃ C : ℝ, ∀ J : ℕ,
      ∑ j ∈ Finset.range J, ∑ n ∈ Finset.Ico (2^j) (2^(j+1)), badTerm n ≤ C := by
  obtain ⟨K, r, j₀, hK, hr0, hr1, hblock⟩ := dyadic_block_bound hpi
  refine ⟨↑j₀ + K * (1 - r)⁻¹, fun J => ?_⟩
  by_cases hJ : J ≤ j₀
  · linarith [show ∑ j ∈ Finset.range J, _ ≤ (↑j₀ : ℝ) from by
      simpa [Nat.min_eq_left hJ] using early_blocks_bound j₀ J,
      mul_nonneg (le_of_lt hK) (inv_nonneg.mpr (sub_nonneg.mpr (le_of_lt hr1)))]
  · push_neg at hJ
    rw [← Finset.sum_range_add_sum_Ico
      (f := fun j => ∑ n ∈ Finset.Ico (2^j) (2^(j+1)), badTerm n) (le_of_lt hJ)]
    linarith [show ∑ j ∈ Finset.range j₀, ∑ n ∈ Finset.Ico (2^j) (2^(j+1)),
        badTerm n ≤ ↑j₀ from by simpa using early_blocks_bound j₀ j₀,
      late_blocks_bound K r j₀ hK hr0 hr1 hblock J]

private lemma summable_badTerm (hpi : PiIrrBound) : Summable badTerm :=
  let ⟨_, hBound⟩ := block_sums_uniformly_bounded hpi
  summable_of_sum_range_le badTerm_nonneg (fun N => (partial_sum_le_block_sums N).trans (hBound _))

private lemma badTerm_pnat (n : ℕ+) :
    badTerm (n : ℕ) = if ¬good n then (1 : ℝ) / (n : ℝ) else 0 := by
  simp only [badTerm, dif_pos n.pos]
  congr 1

private lemma summable_bad_harmonic (hpi : PiIrrBound) :
    Summable fun n : ℕ+ ↦ if ¬good n then (1 : ℝ) / (n : ℝ) else 0 := by
  rw [show (fun n : ℕ+ ↦ if ¬good n then (1 : ℝ) / (n : ℝ) else 0) =
    badTerm ∘ (↑· : ℕ+ → ℕ) from funext fun n => by simp only [Function.comp, badTerm_pnat]]
  exact (summable_badTerm hpi).comp_injective Subtype.val_injective

lemma summable_bad_part (hpi : PiIrrBound) :
    Summable fun n : ℕ+ ↦ if ¬good n then a (n : ℝ) ^ (n : ℕ) / (n : ℝ) else 0 :=
  Summable.of_norm_bounded (summable_bad_harmonic hpi) (fun n => by
    by_cases h : good n
    · simp only [h, ite_false, not_true_eq_false, norm_zero]
      positivity
    · simp only [h, not_false_eq_true, ite_true, Real.norm_of_nonneg (term_nonneg n)]
      exact bad_trivial_bound n)

lemma summable_of_split {α : Type*} {f : α → ℝ} {P : α → Prop}
    (h1 : Summable fun n ↦ if P n then f n else 0)
    (h2 : Summable fun n ↦ if ¬P n then f n else 0) :
    Summable f := by
  rw [show f = fun n => (if P n then f n else 0) + (if ¬P n then f n else 0) from by
    funext n
    by_cases hn : P n <;> simp [hn]]
  exact h1.add h2

theorem borwein_sine_series (hpi : PiIrrBound) :
    Summable fun n : ℕ+ ↦ ((2 / 3 + 1 / 3 * Real.sin (n : ℝ)) ^ (n : ℕ)) / (n : ℝ) := by
  show Summable fun n : ℕ+ ↦ a (n : ℝ) ^ (n : ℕ) / (n : ℝ)
  exact summable_of_split summable_good (summable_bad_part hpi)
