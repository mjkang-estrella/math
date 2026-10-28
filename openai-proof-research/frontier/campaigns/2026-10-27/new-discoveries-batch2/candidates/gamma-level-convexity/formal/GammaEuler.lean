import GammaDefs

/-!
# Genuine closed Euler/Bohr-Mollerup bridge for the gamma level series

For `0 < x < s` the series `seriesTerm x s = fun m => -log (1 - ((s+m)/x)^-2)` has sum
exactly `logDefect x s = log Gamma (s-x) + log Gamma (s+x) - 2 * log Gamma s`.

The bridge is `Real.BohrMollerup.logGammaSeq`:

    logGammaSeq a n = a * log n + log n! - sum_{m in range (n+1)} log (a + m)

combined with `Real.BohrMollerup.tendsto_log_gamma` (which holds for `0 < a` and
converges to `log (Gamma a)`).  Because `seriesTerm x s m = 2 * log (s+m) -
log (s-x+m) - log (s+x+m)`, the finite sums of the series satisfy, for every `n`,

    sum_{m in range (n+1)} seriesTerm x s m
      = logGammaSeq (s-x) n + logGammaSeq (s+x) n - 2 * logGammaSeq s n,

in which the `x * log n` and `log n!` terms cancel identically (finite exact
cancellation, no asymptotic argument).  Since `0 < s - x`, `0 < s + x` and `0 < s`,
each sequence tends to the corresponding `log Gamma` value, and the partial sums of
the (termwise nonnegative) series tend to `logDefect x s`.  Converting the partial
sum limit to a genuine `HasSum` uses `hasSum_iff_tendsto_nat_of_nonneg`.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section
open Set Filter Topology

namespace GammaLevel

/-- For `0 < x < s` and every `n`, the finite partial sum of the series over
`range (n + 1)` equals the mixed Bohr-Mollerup log-gamma sequence.  The `x * log n`
and `log n!` terms cancel identically. -/
theorem finite_sum_eq_logGammaSeq {x s : ℝ} (hx : 0 < x) (hsx : x < s) (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), seriesTerm x s m =
      Real.BohrMollerup.logGammaSeq (s - x) n + Real.BohrMollerup.logGammaSeq (s + x) n -
        2 * Real.BohrMollerup.logGammaSeq s n := by
  have hsx' : 0 < s - x := by linarith
  -- each series term rewrites into log-gamma sequence summands
  have hterm : ∀ m ∈ Finset.range (n + 1), seriesTerm x s m =
      Real.log (s + (m : ℝ)) + Real.log (s + (m : ℝ)) - Real.log ((s - x) + (m : ℝ)) -
        Real.log ((s + x) + (m : ℝ)) := by
    intro m _
    have hsm : 0 < s + (m : ℝ) := by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ (m:ℝ))]
    have hsmx : x < s + (m : ℝ) := by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ (m:ℝ))]
    have hxm1 : 0 < (s - x) + (m : ℝ) := by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ (m:ℝ))]
    have hxm2 : 0 < (s + x) + (m : ℝ) := by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ (m:ℝ))]
    have hinv : ((s + (m : ℝ)) / x)⁻¹ = x / (s + (m : ℝ)) := by field_simp
    have hpow : ((s + (m : ℝ)) / x)⁻¹ ^ 2 = x ^ 2 / (s + (m : ℝ)) ^ 2 := by
      rw [hinv, div_pow]
    have hnum : (s + (m : ℝ)) ^ 2 - x ^ 2 = ((s - x) + (m : ℝ)) * ((s + x) + (m : ℝ)) := by ring
    have hsplit : 1 - ((s + (m : ℝ)) / x)⁻¹ ^ 2
        = ((s - x) + (m : ℝ)) * ((s + x) + (m : ℝ)) / (s + (m : ℝ)) ^ 2 := by
      rw [hpow, one_sub_div (pow_ne_zero 2 (ne_of_gt hsm) :
        (s + (m : ℝ)) ^ 2 ≠ 0), hnum]
    have hdef : seriesTerm x s m = -Real.log (1 - ((s + (m : ℝ)) / x)⁻¹ ^ 2) := rfl
    rw [hdef, hsplit, Real.log_div
      (mul_ne_zero (ne_of_gt hxm1) (ne_of_gt hxm2)) (pow_ne_zero 2 (ne_of_gt hsm)),
      Real.log_mul (ne_of_gt hxm1) (ne_of_gt hxm2), Real.log_pow]
    ring
  calc ∑ m ∈ Finset.range (n + 1), seriesTerm x s m
      = ∑ m ∈ Finset.range (n + 1), (Real.log (s + (m : ℝ)) + Real.log (s + (m : ℝ)) -
          Real.log ((s - x) + (m : ℝ)) - Real.log ((s + x) + (m : ℝ))) :=
        Finset.sum_congr rfl fun m hm => hterm m hm
    _ = -(∑ m ∈ Finset.range (n + 1), Real.log ((s - x) + (m : ℝ)))
        - (∑ m ∈ Finset.range (n + 1), Real.log ((s + x) + (m : ℝ)))
        + 2 * (∑ m ∈ Finset.range (n + 1), Real.log (s + (m : ℝ))) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
        ring
    _ = Real.BohrMollerup.logGammaSeq (s - x) n + Real.BohrMollerup.logGammaSeq (s + x) n -
        2 * Real.BohrMollerup.logGammaSeq s n := by
        simp only [Real.BohrMollerup.logGammaSeq]
        ring

/-- The mixed Bohr-Mollerup log-gamma sequence tends to `logDefect x s`. -/
theorem tendsto_logGammaSeq_mix {x s : ℝ} (hx : 0 < x) (hsx : x < s) :
    Tendsto (fun n : ℕ => Real.BohrMollerup.logGammaSeq (s - x) n +
      Real.BohrMollerup.logGammaSeq (s + x) n - 2 * Real.BohrMollerup.logGammaSeq s n)
      atTop (𝓝 (logDefect x s)) := by
  have h1 : Tendsto (Real.BohrMollerup.logGammaSeq (s - x)) atTop
      (𝓝 (Real.log (Real.Gamma (s - x)))) := Real.BohrMollerup.tendsto_log_gamma (by linarith)
  have h2 : Tendsto (Real.BohrMollerup.logGammaSeq (s + x)) atTop
      (𝓝 (Real.log (Real.Gamma (s + x)))) := Real.BohrMollerup.tendsto_log_gamma (by linarith)
  have h3 : Tendsto (Real.BohrMollerup.logGammaSeq s) atTop
      (𝓝 (Real.log (Real.Gamma s))) := Real.BohrMollerup.tendsto_log_gamma (by linarith)
  have h4 : Tendsto (fun n : ℕ => 2 * Real.BohrMollerup.logGammaSeq s n) atTop
      (𝓝 (2 * Real.log (Real.Gamma s))) := h3.const_mul 2
  have h5 : Tendsto (fun n : ℕ => -(2 * Real.BohrMollerup.logGammaSeq s n)) atTop
      (𝓝 (-(2 * Real.log (Real.Gamma s)))) := h4.neg
  have h6 : Tendsto (fun n : ℕ => Real.BohrMollerup.logGammaSeq (s + x) n +
      -(2 * Real.BohrMollerup.logGammaSeq s n)) atTop
      (𝓝 (Real.log (Real.Gamma (s + x)) + -(2 * Real.log (Real.Gamma s)))) := h2.add h5
  have h7 : Tendsto (fun n : ℕ => Real.BohrMollerup.logGammaSeq (s - x) n +
      (Real.BohrMollerup.logGammaSeq (s + x) n + -(2 * Real.BohrMollerup.logGammaSeq s n)))
      atTop (𝓝 (Real.log (Real.Gamma (s - x)) +
        (Real.log (Real.Gamma (s + x)) + -(2 * Real.log (Real.Gamma s))))) := h1.add h6
  have hfn : (fun n : ℕ => Real.BohrMollerup.logGammaSeq (s - x) n +
      Real.BohrMollerup.logGammaSeq (s + x) n - 2 * Real.BohrMollerup.logGammaSeq s n)
      = fun n : ℕ => Real.BohrMollerup.logGammaSeq (s - x) n +
        (Real.BohrMollerup.logGammaSeq (s + x) n + -(2 * Real.BohrMollerup.logGammaSeq s n)) := by
    funext n; ring
  have hval : Real.log (Real.Gamma (s - x)) +
      (Real.log (Real.Gamma (s + x)) + -(2 * Real.log (Real.Gamma s)))
      = Real.log (Real.Gamma (s - x)) + Real.log (Real.Gamma (s + x)) -
        2 * Real.log (Real.Gamma s) := by
    ring
  rw [hfn]
  have h7' := h7
  rw [hval] at h7'
  exact h7'

/-- The partial sums over `Finset.range n` of `seriesTerm x s` tend to `logDefect x s`. -/
theorem tendsto_partialSum_logDefect {x s : ℝ} (hx : 0 < x) (hsx : x < s) :
    Tendsto (fun n : ℕ => ∑ m ∈ Finset.range n, seriesTerm x s m) atTop
      (𝓝 (logDefect x s)) := by
  have heq := finite_sum_eq_logGammaSeq hx hsx
  have hev : (fun n : ℕ => ∑ m ∈ Finset.range n, seriesTerm x s m)
      =ᶠ[atTop] (fun n : ℕ => Real.BohrMollerup.logGammaSeq (s - x) (n - 1) +
        Real.BohrMollerup.logGammaSeq (s + x) (n - 1) -
          2 * Real.BohrMollerup.logGammaSeq s (n - 1)) := by
    refine Filter.eventually_atTop.mpr ⟨(1 : ℕ), fun n hn => ?_⟩
    have hnn : n = (n - 1) + 1 := by omega
    have hbeta : (fun n : ℕ => Real.BohrMollerup.logGammaSeq (s - x) (n - 1) +
        Real.BohrMollerup.logGammaSeq (s + x) (n - 1) -
          2 * Real.BohrMollerup.logGammaSeq s (n - 1)) (n - 1 + 1)
        = Real.BohrMollerup.logGammaSeq (s - x) (n - 1) +
          Real.BohrMollerup.logGammaSeq (s + x) (n - 1) -
            2 * Real.BohrMollerup.logGammaSeq s (n - 1) := rfl
    rw [hnn, hbeta]
    exact heq (n - 1)
  have hpred : Tendsto (fun n : ℕ => n - 1) atTop atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    refine Filter.eventually_atTop.mpr ⟨b + 1, fun n hn => ?_⟩
    omega
  have hmix := tendsto_logGammaSeq_mix hx hsx
  have hL' : Tendsto (fun n : ℕ => Real.BohrMollerup.logGammaSeq (s - x) (n - 1) +
      Real.BohrMollerup.logGammaSeq (s + x) (n - 1) -
        2 * Real.BohrMollerup.logGammaSeq s (n - 1)) atTop (𝓝 (logDefect x s)) :=
    hmix.comp hpred
  exact Tendsto.congr' hev.symm hL'

/-- Every series term is nonnegative: `0 < x < s` gives `(s+m)/x > 1`, hence
`1 - ((s+m)/x)^-2 ∈ (0, 1]` and its logarithm is nonpositive. -/
theorem seriesTerm_nonneg {x s : ℝ} (hx : 0 < x) (hsx : x < s) :
    ∀ m : ℕ, 0 ≤ seriesTerm x s m := by
  intro m
  have hsm : 0 < s + (m : ℝ) := by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ (m:ℝ))]
  have hsmx : x < s + (m : ℝ) := by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ (m:ℝ))]
  have hinvpos : 0 < ((s + (m : ℝ)) / x)⁻¹ ^ 2 := by positivity
  have hinvlt : ((s + (m : ℝ)) / x)⁻¹ ^ 2 < 1 := by
    have hinv : ((s + (m : ℝ)) / x)⁻¹ = x / (s + (m : ℝ)) := by field_simp
    rw [hinv, div_pow]
    exact div_lt_one (pow_pos hsm 2 : (s + (m : ℝ)) ^ 2 > 0) |>.mpr
      (sq_lt_sq' (by linarith) hsmx)
  have hz1 : 1 - ((s + (m : ℝ)) / x)⁻¹ ^ 2 ≤ 1 := by linarith
  have hlog := Real.log_nonpos (by linarith) hz1
  have hdef : seriesTerm x s m = -Real.log (1 - ((s + (m : ℝ)) / x)⁻¹ ^ 2) := rfl
  rw [hdef]; linarith

/-- **Genuine closed Gamma HasSum bridge.** For `0 < x < s` the series
`seriesTerm x s` converges (as a genuine `HasSum` over `ℕ`) exactly to
`logDefect x s`. -/
theorem gammaHasSum {x s : ℝ} (hx : 0 < x) (hsx : x < s) :
    HasSum (seriesTerm x s) (logDefect x s) :=
  (hasSum_iff_tendsto_nat_of_nonneg (seriesTerm_nonneg hx hsx) _).2
    (tendsto_partialSum_logDefect hx hsx)

/-- Closed-universal form: for all `0 < x < s` the series converges to the defect. -/
theorem gammaHasSum' : ∀ x s : ℝ, 0 < x → x < s → HasSum (seriesTerm x s) (logDefect x s) :=
  fun x s hx hsx => @gammaHasSum x s hx hsx

end GammaLevel
