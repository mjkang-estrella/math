import SourceBridge
import TrigArithmetic
import TrigBridge

open Finset Real

namespace KovalevCounterexample

noncomputable def trigPartial (d n : ℕ) (t : ℝ) : ℝ :=
  ∑ k∈Finset.range (n+1), TrigSource.sourceCoeff (d+1) k*Real.cos ((k:ℝ)*t)

lemma real_certificate_recurrence (k : ℕ) (hk : 1≤k) (hN : k≤949) :
    TrigSource.CoeffRec 50 (fun j => (TrigCertificate.certCoeff j:ℝ)) k := by
  have h := TrigCertificate.certCoeff_recurrence k (by omega) hN
  have hr := congrArg (fun r : ℚ => (r:ℝ)) h
  push_cast at hr
  unfold TrigSource.CoeffRec
  norm_num only [Nat.cast_ofNat]
  have hs : k-50-1=k-51 := by omega
  rw [hs]
  by_cases h50 : 50≤k <;> by_cases h51 : 51≤k <;>
    simp only [h50, h51, ite_true, ite_false] at hr ⊢ <;>
    push_cast at hr <;> linear_combination hr

lemma source_coeff_matches_certificate (k : ℕ) (hk : k≤949) :
    TrigSource.sourceCoeff 50 k=(TrigCertificate.certCoeff k:ℝ) := by
  apply TrigSource.sourceCoeff_matches 50 949 (by norm_num)
    (fun j => (TrigCertificate.certCoeff j:ℝ))
  · exact_mod_cast TrigCertificate.certCoeff_zero
  · exact real_certificate_recurrence
  · exact hk

lemma certificate_scaled_real (k : ℕ) :
    (TrigCertificate.B k:ℝ)=(4:ℝ)^k*(TrigCertificate.certCoeff k:ℝ) := by
  simp only [TrigCertificate.certCoeff, Rat.cast_div, Rat.cast_intCast, Rat.cast_pow,
    Rat.cast_ofNat]
  field_simp

lemma certificate_cosine (k : ℕ) (hk : k≤949) :
    (TrigCertificate.C k:ℝ)=(527:ℝ)^k*Real.cos ((k:ℝ)*TrigBridge.witnessAngle) := by
  apply TrigBridge.integer_cosine_bridge TrigCertificate.C 949
    TrigCertificate.C_zero TrigCertificate.C_one
  · intro n hn
    have h := TrigCertificate.C_recurrence (n+2) (by omega) hn
    simpa only [show n+2-1=n+1 by omega, Nat.add_sub_cancel_right] using h
  · exact hk

theorem certificate_sum_negative :
    (∑ k∈Finset.range 950, (TrigCertificate.certCoeff k:ℝ)*
      Real.cos ((k:ℝ)*TrigBridge.witnessAngle))<0 := by
  apply TrigBridge.negative_sum_of_horner TrigCertificate.B TrigCertificate.C
    TrigCertificate.hornerPrefix (fun k => (TrigCertificate.certCoeff k:ℝ)) 949
  · intro k _
    exact certificate_scaled_real k
  · exact certificate_cosine
  · rfl
  · intro k _
    exact TrigCertificate.hornerPrefix_succ k
  · exact TrigCertificate.hornerValue_neg

/-- An exact negative value for the actual normalized square-root source coefficients. -/
theorem explicit_source_counterexample : trigPartial 49 949 TrigBridge.witnessAngle<0 := by
  unfold trigPartial
  have hs : (∑ k∈Finset.range 950, TrigSource.sourceCoeff 50 k*
      Real.cos ((k:ℝ)*TrigBridge.witnessAngle)) =
      ∑ k∈Finset.range 950, (TrigCertificate.certCoeff k:ℝ)*
        Real.cos ((k:ℝ)*TrigBridge.witnessAngle) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [source_coeff_matches_certificate k (by have := Finset.mem_range.mp hk; omega)]
  change (∑ k∈Finset.range 950, TrigSource.sourceCoeff 50 k*
    Real.cos ((k:ℝ)*TrigBridge.witnessAngle))<0
  rw [hs]
  exact certificate_sum_negative

/-- Kovalev Conjecture 1.3 / MathDB 369172 is false; no zero-free claim is made. -/
theorem conjecture_369172_false :
    ¬∀ (d n : ℕ) (t : ℝ), 2≤d → 0<trigPartial d n t := by
  intro h
  have hp := h 49 949 TrigBridge.witnessAngle (by norm_num)
  have hn := explicit_source_counterexample
  linarith

end KovalevCounterexample
