import SSA5.Main

/-!
# Endpoint: the TC-dominant generating set is not rate-optimal for `m = 5`

Conjecture 1 (arXiv:2304.11403): *When `m` is odd, the generating set `S` with all TC-dominant
length-`m` sequences results in `m`-SSA codes with the largest rate.*  The rate of the
generating set `S` is `lim_{n→∞} (1/n) log₂ |C_n(S)|`.  We show, for `m = 5`, a generating set
`S5` and `ε > 0` with `rate_n(TC) + ε ≤ rate_n(S5)` for all large `n`; consequently the
conjecture fails whether the rate is read as a limit, a limit superior or a limit inferior.
-/

open Filter Topology

namespace SSA

open Classical

theorem card_code_le (m n : ℕ) (S : Set (Word m)) : ((code m n S).card : ℝ) ≤ 4 ^ n := by
  have := Finset.card_le_univ (code m n S)
  simp only [Fintype.card_fun, Fintype.card_fin, card_base] at this
  exact_mod_cast this

theorem logb_two_pow_four (n : ℕ) : Real.logb 2 ((4 : ℝ) ^ n) = 2 * n := by
  rw [Real.logb_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  push_cast; ring

theorem rateSeq_nonneg (m : ℕ) (S : Set (Word m)) (n : ℕ) : 0 ≤ rateSeq m S n := by
  unfold rateSeq
  refine div_nonneg ?_ (Nat.cast_nonneg _)
  rcases Nat.eq_zero_or_pos (code m n S).card with h | h
  · simp [h]
  · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast h)

theorem rateSeq_le_two (m : ℕ) (S : Set (Word m)) (n : ℕ) : rateSeq m S n ≤ 2 := by
  unfold rateSeq
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  rcases Nat.eq_zero_or_pos (code m n S).card with h | h
  · simp [h]
  have h1 : Real.logb 2 ((code m n S).card : ℝ) ≤ Real.logb 2 ((4 : ℝ) ^ n) :=
    Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast h) (card_code_le m n S)
  rw [logb_two_pow_four] at h1
  rw [div_le_iff₀ (by exact_mod_cast hn)]
  linarith

/-- Real form of the lower bound: `|C_{5+k}(S5)| ≥ λᵏ c₁`. -/
theorem lower_real (k : ℕ) :
    ((lamNum : ℝ) / lamDen) ^ k * ((vS [.T, .T, .A, .C, .A] : ℝ) / vMax) ≤
      ((code 5 (5 + k) S5).card : ℝ) := by
  have h := lower_bound k
  have hc := check_consts
  have hD : (0 : ℝ) < (lamDen : ℝ) ^ k * vMax := by
    have : 0 < lamDen := hc.2.2.2.1
    have : 0 < vMax := hc.2.2.2.2.2
    positivity
  have h' : ((lamNum : ℝ) ^ k * vS [.T, .T, .A, .C, .A]) ≤
      (lamDen : ℝ) ^ k * vMax * (code 5 (5 + k) S5).card := by exact_mod_cast h
  rw [div_pow, div_mul_div_comm, div_le_iff₀ hD]
  linarith

/-- Real form of the upper bound: `|C_{5+k}(TC)| ≤ μᵏ c₂`. -/
theorem upper_real (k : ℕ) :
    ((code 5 (5 + k) (TCDominant 5)).card : ℝ) ≤
      ((muNum : ℝ) / muDen) ^ k * (1024 * uMax / uMin) := by
  have h := upper_bound k
  have hc := check_consts
  have hD : (0 : ℝ) < (uMin : ℝ) * (muDen : ℝ) ^ k := by
    have : 0 < muDen := hc.2.2.1
    have : 0 < uMin := hc.2.2.2.2.1
    positivity
  have h' : (uMin : ℝ) * (muDen : ℝ) ^ k * (code 5 (5 + k) (TCDominant 5)).card ≤
      (muNum : ℝ) ^ k * (1024 * uMax) := by exact_mod_cast h
  rw [div_pow, div_mul_div_comm, le_div_iff₀ (by rw [mul_comm]; exact hD)]
  nlinarith

theorem consts_real :
    (0 : ℝ) < (muNum : ℝ) / muDen ∧ (muNum : ℝ) / muDen < (lamNum : ℝ) / lamDen ∧
      (1 : ℝ) < (muNum : ℝ) / muDen ∧ (0 : ℝ) < (vS [.T, .T, .A, .C, .A] : ℝ) / vMax ∧
      (1 : ℝ) ≤ 1024 * (uMax : ℝ) / uMin := by
  have hc := check_consts
  have hw := check_witness.2
  have hb : uMin ≤ uMax := by decide +kernel
  have hm : 649 = muNum ∧ 200 = muDen := ⟨rfl, rfl⟩
  have h1 : (0 : ℝ) < muDen := by exact_mod_cast hc.2.2.1
  have h2 : (0 : ℝ) < lamDen := by exact_mod_cast hc.2.2.2.1
  have h3 : (0 : ℝ) < uMin := by exact_mod_cast hc.2.2.2.2.1
  have h4 : (0 : ℝ) < vMax := by exact_mod_cast hc.2.2.2.2.2
  have h5 : (0 : ℝ) < muNum := by exact_mod_cast hc.2.1
  have h6 : (0 : ℝ) < vS [.T, .T, .A, .C, .A] := by exact_mod_cast hw
  refine ⟨by positivity, ?_, ?_, by positivity, ?_⟩
  · rw [div_lt_div_iff₀ h1 h2]; exact_mod_cast hc.1
  · rw [one_lt_div h1, ← hm.1, ← hm.2]; norm_num
  · rw [le_div_iff₀ h3, one_mul]
    have : (uMin : ℝ) ≤ uMax := by exact_mod_cast hb
    linarith

/-- **Eventual uniform rate gap.** -/
theorem rate_gap : ∃ ε > 0, ∀ᶠ n in atTop,
    rateSeq 5 (TCDominant 5) n + ε ≤ rateSeq 5 S5 n := by
  obtain ⟨hμ0, hml, hμ1, hc1, hc2⟩ := consts_real
  set μ : ℝ := (muNum : ℝ) / muDen
  set lam : ℝ := (lamNum : ℝ) / lamDen
  set c1 : ℝ := (vS [.T, .T, .A, .C, .A] : ℝ) / vMax
  set c2 : ℝ := 1024 * (uMax : ℝ) / uMin
  set L := Real.logb 2 lam
  set M := Real.logb 2 μ
  set δ := L - M
  have hδ : 0 < δ := by
    have := Real.logb_lt_logb (b := 2) (by norm_num) hμ0 hml
    simp only [δ, L, M]; linarith
  have hM : 0 < M := Real.logb_pos (by norm_num) hμ1
  have hC2 : 0 ≤ Real.logb 2 c2 := Real.logb_nonneg (by norm_num) hc2
  set C := Real.logb 2 c1 - Real.logb 2 c2
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (5 * δ - C) / δ)
  refine ⟨δ / 2, by positivity, eventually_atTop.2 ⟨max N 5, fun n hn => ?_⟩⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = 5 + k := ⟨n - 5, by omega⟩
  have hnN : (N : ℝ) ≤ ((5 + k : ℕ) : ℝ) := by exact_mod_cast (le_of_max_le_left hn)
  have hn0 : (0 : ℝ) < ((5 + k : ℕ) : ℝ) := by positivity
  -- lower estimate for log |C_n(S5)|
  have hA : (k : ℝ) * L + Real.logb 2 c1 ≤ Real.logb 2 ((code 5 (5 + k) S5).card : ℝ) := by
    have hlam : 0 < lam := hμ0.trans hml
    have hpos : 0 < lam ^ k * c1 := by positivity
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hpos (lower_real k)
    rw [Real.logb_mul (pow_pos hlam k).ne' hc1.ne', Real.logb_pow] at this
    exact this
  -- upper estimate for log |C_n(TC)|
  have hB : Real.logb 2 ((code 5 (5 + k) (TCDominant 5)).card : ℝ) ≤
      (k : ℝ) * M + Real.logb 2 c2 := by
    rcases Nat.eq_zero_or_pos (code 5 (5 + k) (TCDominant 5)).card with h0 | h0
    · rw [h0]; simp only [Nat.cast_zero, Real.logb_zero]; positivity
    · have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by exact_mod_cast h0) (upper_real k)
      rw [Real.logb_mul (pow_pos hμ0 k).ne' (by linarith), Real.logb_pow] at this
      exact this
  have hkey : ((5 + k : ℕ) : ℝ) * δ > 2 * (5 * δ - C) := by
    have := (div_lt_iff₀ hδ).1 (lt_of_lt_of_le hN hnN)
    linarith
  have hcast : ((5 + k : ℕ) : ℝ) = 5 + k := by push_cast; ring
  unfold rateSeq
  rw [div_add' _ _ _ hn0.ne', div_le_div_iff_of_pos_right hn0]
  rw [hcast] at hkey ⊢
  simp only [δ, C] at hkey ⊢
  nlinarith

theorem bdd_le (m : ℕ) (S : Set (Word m)) : IsBoundedUnder (· ≤ ·) atTop (rateSeq m S) :=
  isBoundedUnder_of ⟨2, rateSeq_le_two m S⟩

theorem bdd_ge (m : ℕ) (S : Set (Word m)) : IsBoundedUnder (· ≥ ·) atTop (rateSeq m S) :=
  isBoundedUnder_of ⟨0, rateSeq_nonneg m S⟩

/-- **Main theorem (limsup reading).**  Conjecture 1 is false: for `m = 5` the
TC-dominant generating set does not have the largest (upper) rate. -/
theorem conjecture1_false_limsup :
    ¬ ∀ m : ℕ, Odd m → ∀ S : Set (Word m), IsGeneratingSet m S →
      limsup (rateSeq m S) atTop ≤ limsup (rateSeq m (TCDominant m)) atTop := by
  intro H
  obtain ⟨ε, hε, hev⟩ := rate_gap
  have h1 := H 5 (by decide) S5 S5_isGeneratingSet
  have h2 : limsup (fun n => rateSeq 5 (TCDominant 5) n + ε) atTop ≤
      limsup (rateSeq 5 S5) atTop :=
    limsup_le_limsup hev
      (isCoboundedUnder_le_of_le atTop (x := ε) fun n => by
        have := rateSeq_nonneg 5 (TCDominant 5) n; linarith)
      (bdd_le 5 S5)
  rw [limsup_add_const atTop _ ε (bdd_le 5 _)
    (isCoboundedUnder_le_of_le atTop (x := 0) (rateSeq_nonneg 5 _))] at h2
  linarith

/-- **Main theorem (liminf reading).** -/
theorem conjecture1_false_liminf :
    ¬ ∀ m : ℕ, Odd m → ∀ S : Set (Word m), IsGeneratingSet m S →
      liminf (rateSeq m S) atTop ≤ liminf (rateSeq m (TCDominant m)) atTop := by
  intro H
  obtain ⟨ε, hε, hev⟩ := rate_gap
  have h1 := H 5 (by decide) S5 S5_isGeneratingSet
  have h2 : liminf (fun n => rateSeq 5 (TCDominant 5) n + ε) atTop ≤
      liminf (rateSeq 5 S5) atTop :=
    liminf_le_liminf hev
      (isBoundedUnder_of ⟨ε, fun n => by have := rateSeq_nonneg 5 (TCDominant 5) n; linarith⟩)
      (isCoboundedUnder_ge_of_le atTop (x := 2) (rateSeq_le_two 5 S5))
  rw [liminf_add_const atTop _ ε
    (isCoboundedUnder_ge_of_le atTop (x := 2) (rateSeq_le_two 5 _)) (bdd_ge 5 _)] at h2
  linarith

/-- **Main theorem (limit reading).**  Whenever the two rates exist as limits, the rate of
`S5` exceeds that of the TC-dominant set. -/
theorem rate_limit_gap : ∃ ε > 0, ∀ a b : ℝ,
    Tendsto (rateSeq 5 S5) atTop (𝓝 a) →
    Tendsto (rateSeq 5 (TCDominant 5)) atTop (𝓝 b) → b + ε ≤ a := by
  obtain ⟨ε, hε, hev⟩ := rate_gap
  exact ⟨ε, hε, fun a b ha hb => le_of_tendsto_of_tendsto (hb.add_const ε) ha hev⟩

/-- Summary endpoint: the explicit generating set `S5` and the TC-dominant set are both members
of `S_5`, and `S5` has strictly larger rate in every reading. -/
theorem conjecture1_false_m5 :
    IsGeneratingSet 5 S5 ∧ IsGeneratingSet 5 (TCDominant 5) ∧
      limsup (rateSeq 5 (TCDominant 5)) atTop < limsup (rateSeq 5 S5) atTop ∧
      liminf (rateSeq 5 (TCDominant 5)) atTop < liminf (rateSeq 5 S5) atTop ∧
      ∃ ε > 0, ∀ᶠ n in atTop, rateSeq 5 (TCDominant 5) n + ε ≤ rateSeq 5 S5 n := by
  obtain ⟨ε, hε, hev⟩ := rate_gap
  refine ⟨S5_isGeneratingSet, TC_isGeneratingSet, ?_, ?_, ε, hε, hev⟩
  · have h2 : limsup (fun n => rateSeq 5 (TCDominant 5) n + ε) atTop ≤
        limsup (rateSeq 5 S5) atTop :=
      limsup_le_limsup hev
        (isCoboundedUnder_le_of_le atTop (x := ε) fun n => by
          have := rateSeq_nonneg 5 (TCDominant 5) n; linarith)
        (bdd_le 5 S5)
    rw [limsup_add_const atTop _ ε (bdd_le 5 _)
      (isCoboundedUnder_le_of_le atTop (x := 0) (rateSeq_nonneg 5 _))] at h2
    linarith
  · have h2 : liminf (fun n => rateSeq 5 (TCDominant 5) n + ε) atTop ≤
        liminf (rateSeq 5 S5) atTop :=
      liminf_le_liminf hev
        (isBoundedUnder_of ⟨ε, fun n => by have := rateSeq_nonneg 5 (TCDominant 5) n; linarith⟩)
        (isCoboundedUnder_ge_of_le atTop (x := 2) (rateSeq_le_two 5 S5))
    rw [liminf_add_const atTop _ ε
      (isCoboundedUnder_ge_of_le atTop (x := 2) (rateSeq_le_two 5 _)) (bdd_ge 5 _)] at h2
    linarith

end SSA
