import PolynomialSources

namespace Davis

def shiftNumerator (d : ℕ) : ℤ := 1000 * (d : ℤ) + Nat.sqrt (1000000 * (d + 2))

def certificateCoeffs (d : ℕ) : List ℤ :=
  coeffTranslate (inequalityCoeffs d) (shiftNumerator d) 2000

def certificateCheck (d : ℕ) : Bool :=
  match certificateCoeffs d with
  | [] => false
  | c :: cs => decide (0 < c) && cs.all (fun z => decide (0 ≤ z))

theorem source_threshold_ge_shift (d : ℕ) :
    (shiftNumerator d : ℝ) / 2000 ≤ ((d : ℝ) + Real.sqrt (d + 2)) / 2 := by
  have hn := Nat.sqrt_le' (1000000 * (d + 2))
  have hnr : (Nat.sqrt (1000000 * (d + 2)) : ℝ) ^ 2 ≤ 1000000 * ((d : ℝ) + 2) := by
    exact_mod_cast hn
  have hs : 0 ≤ Real.sqrt (d + 2 : ℝ) := Real.sqrt_nonneg _
  have hsq : (Real.sqrt (d + 2 : ℝ)) ^ 2 = (d : ℝ) + 2 := Real.sq_sqrt (by positivity)
  have hsqrt : (Nat.sqrt (1000000 * (d + 2)) : ℝ) ≤ 1000 * Real.sqrt (d + 2 : ℝ) := by
    nlinarith
  unfold shiftNumerator
  push_cast
  linarith

theorem certificate_implies_positive {d : ℕ} {x : ℝ} (hc : certificateCheck d = true)
    (hx : ((d : ℝ) + Real.sqrt (d + 2)) / 2 ≤ x) :
    0 < coeffEval (inequalityCoeffs d) x := by
  have hxshift : 0 ≤ x - (shiftNumerator d : ℝ) / 2000 :=
    sub_nonneg.mpr (le_trans (source_threshold_ge_shift d) hx)
  have hpos : 0 < coeffEval (certificateCoeffs d) (x - (shiftNumerator d : ℝ) / 2000) := by
    cases hlist : certificateCoeffs d with
    | nil => simp [certificateCheck, hlist] at hc
    | cons c cs =>
      have hcs : 0 < c ∧ ∀ z ∈ cs, 0 ≤ z := by
        simpa only [certificateCheck, hlist, Bool.and_eq_true, decide_eq_true_eq,
          List.all_eq_true] using hc
      exact coeffEval_pos hcs.1 hcs.2 hxshift
  unfold certificateCoeffs at hpos
  rw [coeffEval_translate _ _ _ (by norm_num)] at hpos
  simp only [Int.cast_ofNat] at hpos
  have heq : x - (shiftNumerator d : ℝ) / 2000 + (shiftNumerator d : ℝ) / 2000 = x := by ring
  rw [heq] at hpos
  have hscale : 0 < (2000 : ℝ) ^ ((inequalityCoeffs d).length - 1) := by positivity
  exact (mul_pos_iff_of_pos_left hscale).mp hpos

end Davis
