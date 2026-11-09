/-
  Part (a) of MathDB 347063: the exact potential.

  With phi = (1 + sqrt 5)/2 and psi = 1/phi = phi - 1, the reviewer's weight is
  w i = i + 2 + psi * (-psi)^i, and -psi = 1 - phi.  Every A1 and every split
  lowers Phi = sum a_i w_i by exactly 1, every Cons i lowers it by exactly i.
-/
import ZeckControls
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Classical

namespace Zeck

noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

noncomputable def psi : ℝ := phi - 1

noncomputable def s : ℝ := 1 - phi

noncomputable def w (i : ℕ) : ℝ := (i : ℝ) + 2 + psi * s ^ i

lemma phi_sq : phi ^ 2 = phi + 1 := by
  unfold phi
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

lemma phi_pos : 0 < phi := by
  unfold phi
  have h0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

lemma psi_def : psi = phi - 1 := rfl

lemma s_def : s = 1 - phi := rfl

lemma s_sq : s ^ 2 = s + 1 := by
  unfold s
  have := phi_sq
  nlinarith

lemma s_cb : s ^ 3 = 2 * s + 1 := by
  have h := s_sq
  nlinarith

lemma psi_phi : psi * phi = 1 := by
  unfold psi
  have := phi_sq
  nlinarith

lemma psi_one_sub_s : psi * (1 - s) = 1 := by
  unfold psi s
  have := phi_sq
  nlinarith

lemma psi_s_eq : psi * s = psi - 1 := by
  have h := psi_one_sub_s
  nlinarith

lemma psi_s2_eq : psi * s ^ 2 = 2 * psi - 1 := by
  have h := psi_s_eq
  have h2 := s_sq
  calc psi * s ^ 2 = psi * (s + 1) := by rw [h2]
    _ = psi * s + psi := by ring
    _ = (psi - 1) + psi := by rw [h]
    _ = 2 * psi - 1 := by ring

lemma psi_s3_eq : psi * s ^ 3 = 3 * psi - 2 := by
  have h := psi_s_eq
  have h2 := s_cb
  calc psi * s ^ 3 = psi * (2 * s + 1) := by rw [h2]
    _ = 2 * (psi * s) + psi := by ring
    _ = 2 * (psi - 1) + psi := by rw [h]
    _ = 3 * psi - 2 := by ring

lemma w_one : w 1 = phi ^ 2 := by
  unfold w
  simp only [pow_one]
  rw [psi_s_eq]
  norm_num
  nlinarith [psi_def, phi_sq]

lemma w_two : w 2 = phi ^ 2 + phi := by
  unfold w
  rw [psi_s2_eq]
  norm_num
  nlinarith [psi_def, phi_sq]

/-- `A1` lowers the potential by exactly one. -/
lemma w_drop_A1 : 2 * w 1 - w 2 = 1 := by
  unfold w
  simp only [pow_one]
  rw [psi_s_eq, psi_s2_eq]
  norm_num
  nlinarith [psi_def, phi_sq]

/-- `Cons i` lowers the potential by exactly `i`. -/
lemma w_drop_cons (i : ℕ) (hi : 2 ≤ i) : w (i - 1) + w i - w (i + 1) = (i : ℝ) := by
  have h1 : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
    rw [Nat.cast_sub (show (1 : ℕ) ≤ i by omega)]
    norm_num
  have h2 : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
  have hp1 : s ^ (i - 1) * s = s ^ i := by
    rw [← pow_succ]
    congr 1
    omega
  have hp2 : s ^ (i - 1) * s ^ 2 = s ^ (i + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hz : 1 + s - s ^ 2 = 0 := by
    have := s_sq
    nlinarith
  have hpsi : psi * s ^ (i - 1) + psi * s ^ i - psi * s ^ (i + 1) = 0 := by
    have e : psi * s ^ (i - 1) + psi * s ^ i - psi * s ^ (i + 1)
        = psi * (s ^ (i - 1) * (1 + s - s ^ 2)) := by
      rw [mul_sub, mul_add, mul_one, ← hp1, ← hp2]
      ring
    rw [e, hz]
    simp
  unfold w
  rw [h1, h2]
  linarith [hpsi]

/-- `Split 2` lowers the potential by exactly one. -/
lemma w_drop_split2 : 2 * w 2 - w 1 - w 3 = 1 := by
  unfold w
  simp only [pow_one]
  rw [psi_s_eq, psi_s2_eq, psi_s3_eq]
  norm_num
  nlinarith [psi_def, phi_sq]

/-- `Split i` for `i ≥ 3` lowers the potential by exactly one. -/
lemma w_drop_splitG (i : ℕ) (hi : 3 ≤ i) : 2 * w i - w (i - 2) - w (i + 1) = 1 := by
  have h1 : ((i - 2 : ℕ) : ℝ) = (i : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have h2 : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
  have hp1 : s ^ (i - 2) * s ^ 2 = s ^ i := by
    rw [← pow_add]
    congr 1
    omega
  have hp2 : s ^ (i - 2) * s ^ 3 = s ^ (i + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hz : 2 * s ^ 2 - 1 - s ^ 3 = 0 := by
    have h1 := s_sq
    have h2 := s_cb
    nlinarith
  have hpsi : 2 * (psi * s ^ i) - psi * s ^ (i - 2) - psi * s ^ (i + 1) = 0 := by
    have e1 : psi * s ^ i = psi * s ^ (i - 2) * s ^ 2 := by
      rw [← hp1]; ring
    have e2 : psi * s ^ (i + 1) = psi * s ^ (i - 2) * s ^ 3 := by
      rw [← hp2]; ring
    rw [e1, e2]
    have e3 : 2 * (psi * s ^ (i - 2) * s ^ 2) - psi * s ^ (i - 2) - psi * s ^ (i - 2) * s ^ 3
        = psi * s ^ (i - 2) * (2 * s ^ 2 - 1 - s ^ 3) := by ring
    rw [e3, hz]
    ring
  unfold w
  rw [h1, h2]
  linarith [hpsi]

/-! ### The potential -/

/-- The exact potential `Phi a = sum_i a_i * w i`. -/
noncomputable def Phi (a : Pos) : ℝ := a.sum (fun i c => (c : ℝ) * w i)

lemma sum_update_Phi (a : Pos) (i v : ℕ) :
    Phi (a.update i v) + (a i : ℝ) * w i = Phi a + (v : ℝ) * w i := by
  unfold Phi
  exact Finsupp.sum_update_add a i v (fun j c => (c : ℝ) * w j) (by intro j; simp)
    (by intro j x y; push_cast; ring)

lemma Phi_start (n : ℕ) : Phi (start n) = (n : ℝ) * phi ^ 2 := by
  have h : Phi (start n) = (n : ℝ) * w 1 := by simp [Phi, start]
  rw [h, w_one]

lemma Phi_doA1 (a : Pos) (h : legalA1 a) : Phi (doA1 a) = Phi a - 1 := by
  have ha : 2 ≤ a 1 := h
  have e1 := sum_update_Phi a 1 (a 1 - 2)
  have e2 := sum_update_Phi (a.update 1 (a 1 - 2)) 2 (a 2 + 1)
  have h1 : (a.update 1 (a 1 - 2)) 2 = a 2 := by
    have hne : (2 : ℕ) ≠ 1 := by norm_num
    simp [Finsupp.update_apply, hne]
  rw [h1] at e2
  have hc : ((a 1 - 2 : ℕ) : ℝ) = (a 1 : ℝ) - 2 := by
    rw [Nat.cast_sub ha]; norm_num
  have hc2 : ((a 2 + 1 : ℕ) : ℝ) = (a 2 : ℝ) + 1 := by push_cast; ring
  rw [hc] at e1
  rw [hc2] at e2
  unfold doA1
  linarith [e1, e2, w_drop_A1]

lemma Phi_doCons (a : Pos) (i : ℕ) (h : legalCons a i) : Phi (doCons a i) = Phi a - (i : ℝ) := by
  obtain ⟨hi2, hi1, hi0⟩ := h
  have e1 := sum_update_Phi a (i - 1) (a (i - 1) - 1)
  have e2 := sum_update_Phi (a.update (i - 1) (a (i - 1) - 1)) i (a i - 1)
  have e3 := sum_update_Phi ((a.update (i - 1) (a (i - 1) - 1)).update i (a i - 1))
    (i + 1) (a (i + 1) + 1)
  have h1 : (a.update (i - 1) (a (i - 1) - 1)) i = a i := by
    have hne : i ≠ i - 1 := by omega
    simp [Finsupp.update_apply, hne]
  have h2 : ((a.update (i - 1) (a (i - 1) - 1)).update i (a i - 1)) (i + 1) = a (i + 1) := by
    rw [Finsupp.update_apply, Finsupp.update_apply]
    split_ifs with h1 h2
    · omega
    · omega
    · rfl
  rw [h1] at e2
  rw [h2] at e3
  have hc1 : ((a (i - 1) - 1 : ℕ) : ℝ) = (a (i - 1) : ℝ) - 1 := by
    rw [Nat.cast_sub hi1]; norm_num
  have hc2 : ((a i - 1 : ℕ) : ℝ) = (a i : ℝ) - 1 := by
    rw [Nat.cast_sub hi0]; norm_num
  have hc3 : ((a (i + 1) + 1 : ℕ) : ℝ) = (a (i + 1) : ℝ) + 1 := by push_cast; ring
  rw [hc1] at e1
  rw [hc2] at e2
  rw [hc3] at e3
  unfold doCons
  linarith [e1, e2, e3, w_drop_cons i hi2]

lemma Phi_doSplit2 (a : Pos) (h : 2 ≤ a 2) : Phi (doSplit2 a) = Phi a - 1 := by
  have e1 := sum_update_Phi a 2 (a 2 - 2)
  have e2 := sum_update_Phi (a.update 2 (a 2 - 2)) 1 (a 1 + 1)
  have e3 := sum_update_Phi ((a.update 2 (a 2 - 2)).update 1 (a 1 + 1)) 3 (a 3 + 1)
  have h1 : (a.update 2 (a 2 - 2)) 1 = a 1 := by
    have hne : (1 : ℕ) ≠ 2 := by norm_num
    simp [Finsupp.update_apply, hne]
  have h2 : ((a.update 2 (a 2 - 2)).update 1 (a 1 + 1)) 3 = a 3 := by
    rw [Finsupp.update_apply, Finsupp.update_apply]
    split_ifs with h1 h2
    · omega
    · omega
    · rfl
  rw [h1] at e2
  rw [h2] at e3
  have hc : ((a 2 - 2 : ℕ) : ℝ) = (a 2 : ℝ) - 2 := by
    rw [Nat.cast_sub h]; norm_num
  have hc2 : ((a 1 + 1 : ℕ) : ℝ) = (a 1 : ℝ) + 1 := by push_cast; ring
  have hc3 : ((a 3 + 1 : ℕ) : ℝ) = (a 3 : ℝ) + 1 := by push_cast; ring
  rw [hc] at e1
  rw [hc2] at e2
  rw [hc3] at e3
  unfold doSplit2
  linarith [e1, e2, e3, w_drop_split2]

lemma Phi_doSplitG (a : Pos) (i : ℕ) (hi : 3 ≤ i) (hge : 2 ≤ a i) :
    Phi (doSplitG a i) = Phi a - 1 := by
  have e1 := sum_update_Phi a i (a i - 2)
  have e2 := sum_update_Phi (a.update i (a i - 2)) (i - 2) (a (i - 2) + 1)
  have e3 := sum_update_Phi ((a.update i (a i - 2)).update (i - 2) (a (i - 2) + 1))
    (i + 1) (a (i + 1) + 1)
  have h1 : (a.update i (a i - 2)) (i - 2) = a (i - 2) := by
    have hne : i - 2 ≠ i := by omega
    simp [Finsupp.update_apply, hne]
  have h2 : ((a.update i (a i - 2)).update (i - 2) (a (i - 2) + 1)) (i + 1) = a (i + 1) := by
    rw [Finsupp.update_apply, Finsupp.update_apply]
    split_ifs with h1 h2
    · omega
    · omega
    · rfl
  rw [h1] at e2
  rw [h2] at e3
  have hc : ((a i - 2 : ℕ) : ℝ) = (a i : ℝ) - 2 := by
    rw [Nat.cast_sub hge]; norm_num
  have hc2 : ((a (i - 2) + 1 : ℕ) : ℝ) = (a (i - 2) : ℝ) + 1 := by push_cast; ring
  have hc3 : ((a (i + 1) + 1 : ℕ) : ℝ) = (a (i + 1) : ℝ) + 1 := by push_cast; ring
  rw [hc] at e1
  rw [hc2] at e2
  rw [hc3] at e3
  unfold doSplitG
  linarith [e1, e2, e3, w_drop_splitG i hi]

lemma Phi_doSplit (a : Pos) (i : ℕ) (h : legalSplit a i) : Phi (doSplit a i) = Phi a - 1 := by
  obtain ⟨hi, h2⟩ := h
  rcases eq_or_lt_of_le hi with h' | h'
  · have hi2 : i = 2 := by omega
    subst hi2
    have e : doSplit a 2 = doSplit2 a := by simp [doSplit]
    rw [e]
    exact Phi_doSplit2 a h2
  · have h1 : i ≠ 1 := by omega
    have h3 : i ≠ 2 := by omega
    have e : doSplit a i = doSplitG a i := by simp [doSplit, h1, h3]
    rw [e]
    exact Phi_doSplitG a i (by omega) h2

/-! ### The drop of a Split Smallest step -/

noncomputable def dropSS (a : Pos) : ℕ :=
  match smallestSplit a with
  | some _ => 1
  | none =>
    if legalA1 a then 1
    else match smallestCons a with
         | some i => i
         | none => 0

lemma Phi_stepSS (a : Pos) : Phi (stepSS a) = Phi a - (dropSS a : ℝ) := by
  unfold stepSS dropSS
  cases hsp : smallestSplit a with
  | some i =>
    dsimp only
    rw [Phi_doSplit a i (smallestSplit_some_spec a hsp).1]
    norm_num
  | none =>
    dsimp only
    split_ifs with ha1
    · rw [Phi_doA1 a ha1]
      norm_num
    · cases hco : smallestCons a with
      | some i =>
        dsimp only
        rw [Phi_doCons a i (smallestCons_some_spec a hco).1]
      | none =>
        dsimp only
        ring

lemma Phi_run (n : ℕ) (k : ℕ) :
    Phi (run stepSS (start n) k) =
      Phi (start n) - Finset.sum (Finset.range k) (fun j => (dropSS (run stepSS (start n) j) : ℝ)) := by
  induction k with
  | zero => simp [run]
  | succ k ih =>
    rw [run_succ, Phi_stepSS, ih, Finset.sum_range_succ]
    ring

end Zeck
