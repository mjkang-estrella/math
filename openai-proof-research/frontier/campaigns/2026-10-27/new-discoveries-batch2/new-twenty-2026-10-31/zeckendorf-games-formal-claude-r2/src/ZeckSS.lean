/-
  Part (a) of MathDB 347063: the lower half of the Split Smallest estimate.
  A combine at index at least two only happens once every count is at most one,
  so the chip count is at most `2 log₂ n + 2` from that moment on.
-/
import ZeckChain

open Classical

set_option linter.unusedSimpArgs false

namespace Zeck

/-- A step never drops the potential by more than the bound on the index, and any excess is
paid for by a lost chip. -/
lemma step_excess (a : Pos) (n : ℕ) (hv : val a = n) (hm : hasMove a) :
    (dropSS a : ℝ) - 1 ≤ (2 * (Nat.log2 n : ℝ) + 1) * ((chips a : ℝ) - chips (stepSS a)) := by
  have hK : (0 : ℝ) ≤ 2 * (Nat.log2 n : ℝ) + 1 := by positivity
  unfold stepSS dropSS
  cases hsp : smallestSplit a with
  | some i =>
    dsimp only
    rw [chips_doSplit a i (smallestSplit_some_spec a hsp).1]
    simp
  | none =>
    dsimp only
    split_ifs with hA
    · have h1 := chips_doA1 a hA
      have h2 : (chips (doA1 a) : ℝ) + 1 = (chips a : ℝ) := by exact_mod_cast h1
      have h3 : (chips a : ℝ) - chips (doA1 a) = 1 := by linarith
      rw [h3]
      simp
      linarith
    · cases hco : smallestCons a with
      | some i =>
        dsimp only
        have hl := (smallestCons_some_spec a hco).1
        have h1 := chips_doCons a i hl
        have h2 : (chips (doCons a i) : ℝ) + 1 = (chips a : ℝ) := by exact_mod_cast h1
        have h3 : (chips a : ℝ) - chips (doCons a i) = 1 := by linarith
        rw [h3]
        have hi : i ≤ 2 * Nat.log2 n + 1 := idx_bound a n hv i hl.2.2
        have hi' : (i : ℝ) ≤ 2 * (Nat.log2 n : ℝ) + 1 := by exact_mod_cast hi
        linarith
      | none =>
        dsimp only
        exfalso
        rcases hm with ha | hc | hs
        · exact hA ha
        · exact (smallestCons_none_iff a).1 hco hc
        · exact (smallestSplit_none_iff a).1 hsp hs

lemma drop_ge_two_spec (a : Pos) (h : 2 ≤ dropSS a) : smallestSplit a = none ∧ ¬ legalA1 a := by
  unfold dropSS at h
  cases hsp : smallestSplit a with
  | some i =>
    rw [hsp] at h
    dsimp only at h
    omega
  | none =>
    rw [hsp] at h
    dsimp only at h
    split_ifs at h with hA
    · omega
    · exact ⟨rfl, hA⟩

/-- The excess is bounded by the chip count at the first genuine combine. -/
theorem SS_excess_le (n : ℕ) :
    Finset.sum (Finset.range (SS n)) (fun j => (dropSS (run stepSS (start n) j) : ℝ) - 1)
      ≤ (2 * (Nat.log2 n : ℝ) + 1) * (2 * (Nat.log2 n : ℝ) + 2) := by
  have hK : (0 : ℝ) ≤ 2 * (Nat.log2 n : ℝ) + 1 := by positivity
  by_cases hex : ∃ j, j < SS n ∧ 2 ≤ dropSS (run stepSS (start n) j)
  · let j0 := Nat.find hex
    have hj0 : j0 < SS n ∧ 2 ≤ dropSS (run stepSS (start n) j0) := Nat.find_spec hex
    have hmin : ∀ t, t < j0 → t < SS n → dropSS (run stepSS (start n) t) ≤ 1 := by
      intro t ht htN
      by_contra hc
      exact Nat.find_min hex ht ⟨htN, by omega⟩
    have hspec := drop_ge_two_spec _ hj0.2
    have hchips : chips (run stepSS (start n) j0) ≤ 2 * Nat.log2 n + 2 :=
      chips_le_of_all_one _ n (runSS_val n j0) (runSS_zero n j0)
        (stepSS_cons_le_one _ hspec.1 hspec.2)
    let G : ℕ → ℝ := fun t =>
      if t ≤ j0 then (2 * (Nat.log2 n : ℝ) + 1) * (2 * (Nat.log2 n : ℝ) + 2)
      else (2 * (Nat.log2 n : ℝ) + 1) * (chips (run stepSS (start n) t) : ℝ)
    have hG0 : G 0 = (2 * (Nat.log2 n : ℝ) + 1) * (2 * (Nat.log2 n : ℝ) + 2) := by
      simp [G]
    have hGnn : ∀ t, 0 ≤ G t := by
      intro t
      simp only [G]
      split_ifs
      · positivity
      · positivity
    have hstep : ∀ t, t ≤ SS n →
        Finset.sum (Finset.range t) (fun j => (dropSS (run stepSS (start n) j) : ℝ) - 1) + G t
          ≤ G 0 := by
      intro t
      induction t with
      | zero =>
        intro _
        simp
      | succ t ih =>
        intro ht
        have ih' := ih (by omega)
        rw [Finset.sum_range_succ]
        have htN : t < SS n := by omega
        have hm : hasMove (run stepSS (start n) t) :=
          gameLen_min stepSS stepSS_drop (start n) t htN
        have hdiff := step_excess _ n (runSS_val n t) hm
        have hK1 : (0 : ℝ) ≤ (2 * (Nat.log2 n : ℝ) + 1) := hK
        have key : (dropSS (run stepSS (start n) t) : ℝ) - 1 + G (t + 1) ≤ G t := by
          by_cases h1 : t < j0
          · have hd := hmin t h1 htN
            have hd' : (dropSS (run stepSS (start n) t) : ℝ) ≤ 1 := by exact_mod_cast hd
            have ht1 : t + 1 ≤ j0 := by omega
            have ht2 : t ≤ j0 := by omega
            simp only [G, ht1, ht2, ite_true]
            linarith
          · by_cases h2 : t = j0
            · have ht1 : ¬ t + 1 ≤ j0 := by omega
              have ht2 : t ≤ j0 := by omega
              simp only [G, ht1, ht2, ite_true, ite_false]
              have hc' : (chips (run stepSS (start n) j0) : ℝ) ≤ 2 * (Nat.log2 n : ℝ) + 2 := by
                exact_mod_cast hchips
              rw [← h2] at hc'
              have h3 : (2 * (Nat.log2 n : ℝ) + 1) * (chips (run stepSS (start n) t) : ℝ)
                  ≤ (2 * (Nat.log2 n : ℝ) + 1) * (2 * (Nat.log2 n : ℝ) + 2) :=
                mul_le_mul_of_nonneg_left hc' hK1
              rw [run_succ] at *
              nlinarith
            · have ht1 : ¬ t + 1 ≤ j0 := by omega
              have ht2 : ¬ t ≤ j0 := by omega
              simp only [G, ht1, ht2, ite_false]
              rw [run_succ]
              nlinarith
        linarith
    have hN := hstep (SS n) (le_refl _)
    rw [hG0] at hN
    have := hGnn (SS n)
    linarith
  · have hall : ∀ j ∈ Finset.range (SS n), (dropSS (run stepSS (start n) j) : ℝ) - 1 ≤ 0 := by
      intro j hj
      have hjN : j < SS n := Finset.mem_range.1 hj
      have h1 : dropSS (run stepSS (start n) j) ≤ 1 := by
        by_contra hc
        exact hex ⟨j, hjN, by omega⟩
      have h2 : (dropSS (run stepSS (start n) j) : ℝ) ≤ 1 := by exact_mod_cast h1
      linarith
    have hsum := Finset.sum_nonpos hall
    have hpos : (0 : ℝ) ≤ (2 * (Nat.log2 n : ℝ) + 1) * (2 * (Nat.log2 n : ℝ) + 2) := by positivity
    linarith

/-- The Split Smallest deficit at the end of the game. -/
lemma SS_final_Phi_le (n : ℕ) :
    Phi (run stepSS (start n) (SS n)) ≤ (2 * (Nat.log2 n : ℝ) + 2) * (2 * (Nat.log2 n : ℝ) + 4) := by
  have hterm : ¬ hasMove (run stepSS (start n) (SS n)) :=
    gameLen_spec stepSS stepSS_drop (start n)
  have hchips : chips (run stepSS (start n) (SS n)) ≤ 2 * Nat.log2 n + 2 :=
    chips_le_of_all_one _ n (runSS_val n _) (runSS_zero n _)
      (fun j hj => terminal_le_one _ hterm hj)
  have hc' : (chips (run stepSS (start n) (SS n)) : ℝ) ≤ 2 * (Nat.log2 n : ℝ) + 2 := by
    exact_mod_cast hchips
  have hP := Phi_le_chips_mul (run stepSS (start n) (SS n)) (2 * Nat.log2 n + 1) (by
    intro i hi
    by_contra hc
    have : 1 ≤ (run stepSS (start n) (SS n)) i := by omega
    have := runSS_idx n (SS n) i this
    omega)
  push_cast at hP
  have hL : (0 : ℝ) ≤ (Nat.log2 n : ℝ) := Nat.cast_nonneg _
  have e : (2 * (Nat.log2 n : ℝ) + 1 + 3) = 2 * (Nat.log2 n : ℝ) + 4 := by ring
  rw [e] at hP
  have h4 : (chips (run stepSS (start n) (SS n)) : ℝ) * (2 * (Nat.log2 n : ℝ) + 4)
      ≤ (2 * (Nat.log2 n : ℝ) + 2) * (2 * (Nat.log2 n : ℝ) + 4) :=
    mul_le_mul_of_nonneg_right hc' (by positivity)
  linarith

/-- The Split Smallest estimate. -/
theorem SS_estimate :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → |(SS n : ℝ) - phi ^ 2 * n| ≤ C * (Real.log n) ^ 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨40 / (Real.log 2) ^ 2, fun n hn => ?_⟩
  have hdef := SS_deficit n
  have hex := SS_excess_nonneg n
  have hP0 := Phi_nonneg (run stepSS (start n) (SS n))
  have hEx := SS_excess_le n
  have hPh := SS_final_Phi_le n
  set l : ℝ := (Nat.log2 n : ℝ) with hl
  have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg _
  have hdef1 : phi ^ 2 * n - (SS n : ℝ) ≤ 10 * (l + 1) ^ 2 := by
    rw [hdef]
    nlinarith
  have hdef0 : 0 ≤ phi ^ 2 * n - (SS n : ℝ) := by
    rw [hdef]
    linarith
  have hlog : l + 1 ≤ 2 * Real.log n / Real.log 2 := by
    have hn0 : n ≠ 0 := by omega
    have hp := Nat.pow_log_le_self 2 hn0
    rw [← Nat.log2_eq_log_two] at hp
    have hpR : (2 : ℝ) ^ Nat.log2 n ≤ (n : ℝ) := by exact_mod_cast hp
    have hlogp := Real.log_le_log (by positivity) hpR
    rw [Real.log_pow] at hlogp
    have h2n : Real.log 2 ≤ Real.log n :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have e1 : l * Real.log 2 ≤ Real.log n := hlogp
    have e2 : 2 * Real.log n / Real.log 2 = (2 * Real.log n) * (1 / Real.log 2) := by ring
    rw [le_div_iff₀ hl2]
    nlinarith
  have hsq : (l + 1) ^ 2 ≤ (2 * Real.log n / Real.log 2) ^ 2 := by
    have h0 : 0 ≤ l + 1 := by linarith
    gcongr
  have e3 : 10 * (2 * Real.log n / Real.log 2) ^ 2 = 40 / (Real.log 2) ^ 2 * (Real.log n) ^ 2 := by
    field_simp
    ring
  rw [abs_sub_comm, abs_of_nonneg hdef0]
  calc phi ^ 2 * n - (SS n : ℝ) ≤ 10 * (l + 1) ^ 2 := hdef1
    _ ≤ 10 * (2 * Real.log n / Real.log 2) ^ 2 := by gcongr
    _ = 40 / (Real.log 2) ^ 2 * (Real.log n) ^ 2 := e3

end Zeck
