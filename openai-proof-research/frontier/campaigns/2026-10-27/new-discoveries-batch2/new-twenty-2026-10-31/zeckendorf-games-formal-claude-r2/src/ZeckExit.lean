/-
  Part (b) of MathDB 347063: the endgame of a level, split by the pool size `K = m` and by the
  Case 1 / 2 / 3 trichotomy of the reviewer's erratum.  Combines outrank splits, so the order of
  the high and low moves differs between cases; a repeat at `p - 2` fires only after the
  high combines.

  Case 2 is `z (q-1) = 1`, where the combine `C_{p-2}` fires at once.  Cases 1 and 3 are
  `z (q-1) = 0` with `z q = 0` or `z q = 1`.
-/
import ZeckMacro

open Classical

set_option linter.unusedSimpArgs false

namespace Zeck

open Finsupp (single)

lemma W_shift1 (q c3 : ℕ) : W q 0 1 0 c3 0 0 = single (q + 2) 1 + W (q + 2) 0 c3 0 0 0 0 := by
  ext t
  simp only [Finsupp.add_apply, Finsupp.single_apply, W_apply]
  split_ifs <;> omega

lemma high_m4 {L : Pos} {q : ℕ} (hq : q % 2 = 0) (hq1 : 1 ≤ q) (hL : LowQ L q) (hL0 : L q = 0)
    (hL2 : L (q + 2) = 0) (m : ℕ) :
    Tr (L + W q 1 1 0 (m + 2) 0 0) 3 2 (L + W (q + 2) 0 m 0 1 0 0) := by
  have hLq : LowQ L (q + 2) := hL.mono (by omega)
  have s1 : Tr (L + W q 1 1 0 (m + 2) 0 0) 1 1 (L + W q 0 0 1 (m + 2) 0 0) :=
    Tr_Cp hL hL0 hq 0 0 0 (m + 2) 0 0 (Or.inl hq1)
  have e : W q 0 0 1 (m + 2) 0 0 = W (q + 2) 1 (m + 2) 0 0 0 0 := W_shift q 1 (m + 2) 0 0
  rw [e] at s1
  have s2 : Tr (L + W (q + 2) 1 (m + 2) 0 0 0 0) 1 1 (L + W (q + 2) 0 (m + 1) 1 0 0 0) :=
    Tr_Cp hLq hL2 (by omega) 0 (m + 1) 0 0 0 0 (Or.inl (by omega))
  have s3 : Tr (L + W (q + 2) 0 (m + 1) 1 0 0 0) 1 0 (L + W (q + 2) 0 m 0 1 0 0) :=
    Tr_Cp1 hLq (by omega) m 0 0 0 0
  exact (s1.trans s2).trans s3

/-- The endgame at a level `p = q + 2 ≥ 4`. -/
theorem exit_step {z : Pos} {q : ℕ} (hq : q % 2 = 0) (hq2 : 2 ≤ q) (hz : Zk z q)
    (m M0 : ℕ) (hm : m ≤ 4) :
    ∃ z' k e m' h', Zk z' (q + 2) ∧ h' ≤ 2 ∧
      Tr (B z q m (M0 + 4)) k e (B z' (q + 2) m' h') ∧
      e ≤ k ∧ k ≤ e + 2 ∧ M0 ≤ m' ∧ m' ≤ M0 + 5 := by
  have hq2' : (q + 2) % 2 = 0 := by omega
  have hm' : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
  rcases hm' with rfl | rfl | rfl | rfl | rfl
  · -- `K = 0`: the pool is empty, relabel.
    have e : B z q 0 (M0 + 4) = B z (q + 2) (M0 + 4) 0 := by
      show z + W q 0 0 0 (M0 + 4) 0 0 = z + W (q + 2) 0 (M0 + 4) 0 0 0 0
      rw [W_shift]
    refine ⟨z, 0, 0, M0 + 4, 0, hz.mono (by omega), by omega, ?_, by omega, by omega, by omega,
      by omega⟩
    rw [e]
    exact Tr.refl _
  · -- `K = 1`: the single pool chip stays in the low state.
    have e : B z q 1 (M0 + 4) = B (z + single (q + 2) 1) (q + 2) (M0 + 4) 0 := by
      show z + W q 0 1 0 (M0 + 4) 0 0 = (z + single (q + 2) 1) + W (q + 2) 0 (M0 + 4) 0 0 0 0
      rw [W_shift1, add_assoc]
    have hzz : Zk (z + single (q + 2) 1) (q + 2) :=
      hz.addAt (by omega) (hz.top _ (by omega)) (hz.top _ (by omega)) (hz.top _ (by omega))
        (by omega) (le_refl _)
    refine ⟨_, 0, 0, M0 + 4, 0, hzz, by omega, ?_, by omega, by omega, by omega, by omega⟩
    rw [e]
    exact Tr.refl _
  · -- `K = 2`: `S_p` leaves the pool empty.
    have s1 : Tr (B z q 2 (M0 + 4)) 1 1 (z + single q 1 + W q 0 0 1 (M0 + 4) 0 0) :=
      Tr_Sp hq2 hq hz 0 (M0 + 4)
    by_cases h1 : z (q - 1) = 1
    · -- Case 2: the chip at `p - 1` stays low because `a_p = 0`.
      have hq0 : z q = 0 := by
        have := hz.adj (q - 1)
        rw [show q - 1 + 1 = q by omega] at this
        omega
      have s2 := Tr_low_cons (H := W q 0 0 1 (M0 + 4) 0 0) hq2 hq hz h1 (fun i hi => W_below hi)
      have hz1 : Zk (z.update (q - 1) 0) q := hz.erase (q - 1) q (fun x hx _ => hz.top x hx)
      have hZ : Zk (z.update (q - 1) 0 + single (q + 1) 1) (q + 1) := by
        refine hz1.addAt (by omega) ?_ ?_ ?_ (by omega) (le_refl _)
        · have hne : q + 1 ≠ q - 1 := by omega
          simp [Finsupp.update_apply, hne]
          exact hz.top _ (by omega)
        · rw [show q + 1 - 1 = q by omega]
          have hne : q ≠ q - 1 := by omega
          simp [Finsupp.update_apply, hne, hq0]
        · have hne : q + 1 + 1 ≠ q - 1 := by omega
          simp [Finsupp.update_apply, hne]
          exact hz.top _ (by omega)
      have hLq := (hZ.mono (show q + 1 ≤ q + 2 by omega)).lowQ
      have hL0 : (z.update (q - 1) 0 + single (q + 1) 1 : Pos) (q + 2) = 0 :=
        hZ.top _ (by omega)
      have e : W q 0 0 1 (M0 + 4) 0 0 = W (q + 2) 1 (M0 + 4) 0 0 0 0 := W_shift q 1 (M0 + 4) 0 0
      rw [e] at s1 s2
      have s3 : Tr (z.update (q - 1) 0 + single (q + 1) 1 + W (q + 2) 1 (M0 + 4) 0 0 0 0) 1 1
          (z.update (q - 1) 0 + single (q + 1) 1 + W (q + 2) 0 (M0 + 3) 1 0 0 0) :=
        Tr_Cp hLq hL0 hq2' 0 (M0 + 3) 0 0 0 0 (Or.inl (by omega))
      have s4 : Tr (z.update (q - 1) 0 + single (q + 1) 1 + W (q + 2) 0 (M0 + 3) 1 0 0 0) 1 0
          (z.update (q - 1) 0 + single (q + 1) 1 + W (q + 2) 0 (M0 + 2) 0 1 0 0) :=
        Tr_Cp1 hLq hq2' (M0 + 2) 0 0 0 0
      exact ⟨_, 4, 3, M0 + 2, 1, hZ.mono (by omega), by omega,
        (((s1.trans s2).trans s3).trans s4), by omega, by omega, by omega, by omega⟩
    · -- Cases 1 and 3: the high combines first, then the quiet insertion.
      have h0 : z (q - 1) = 0 := by
        have := hz.one (q - 1)
        omega
      have hLq0 : LowQ (z + single q 1) q := hz.lowQ_add hq2 h0
      have hLq := hLq0.mono (show q ≤ q + 2 by omega)
      have hL0 : (z + single q 1 : Pos) (q + 2) = 0 := hLq0.top _ (by omega)
      have e : W q 0 0 1 (M0 + 4) 0 0 = W (q + 2) 1 (M0 + 4) 0 0 0 0 := W_shift q 1 (M0 + 4) 0 0
      rw [e] at s1
      have s3 : Tr (z + single q 1 + W (q + 2) 1 (M0 + 4) 0 0 0 0) 1 1
          (z + single q 1 + W (q + 2) 0 (M0 + 3) 1 0 0 0) :=
        Tr_Cp hLq hL0 hq2' 0 (M0 + 3) 0 0 0 0 (Or.inl (by omega))
      have s4 : Tr (z + single q 1 + W (q + 2) 0 (M0 + 3) 1 0 0 0) 1 0
          (z + single q 1 + W (q + 2) 0 (M0 + 2) 0 1 0 0) :=
        Tr_Cp1 hLq hq2' (M0 + 2) 0 0 0 0
      have hI : Inert (W (q + 2) 0 (M0 + 2) 0 1 0 0) q := Inert_W (by omega) (M0 + 2) 1 0
      obtain ⟨z', k', hz', hT⟩ := cascade q hq hq2 z _ hz hI
      refine ⟨z', 1 + 1 + 1 + k', 1 + 1 + 0 + k', M0 + 2, 1, hz'.mono (by omega), by omega,
        ((s1.trans s3).trans s4).trans hT, by omega, by omega, by omega, by omega⟩
  · -- `K = 3`.
    have s1 : Tr (B z q 3 (M0 + 4)) 1 1 (z + single q 1 + W q 0 1 1 (M0 + 4) 0 0) :=
      Tr_Sp hq2 hq hz 1 (M0 + 4)
    by_cases h1 : z (q - 1) = 1
    · -- Case 2: `C_{p-2}`, then `C_p`, then the doubled exit.
      have hq0 : z q = 0 := by
        have := hz.adj (q - 1)
        rw [show q - 1 + 1 = q by omega] at this
        omega
      have s2 := Tr_low_cons (H := W q 0 1 1 (M0 + 4) 0 0) hq2 hq hz h1 (fun i hi => W_below hi)
      rw [reshape_c0] at s2
      have hz1 : Zk (z.update (q - 1) 0) q := hz.erase (q - 1) q (fun x hx _ => hz.top x hx)
      have hL0 : (z.update (q - 1) 0) q = 0 := by
        have hne : q ≠ q - 1 := by omega
        simp [Finsupp.update_apply, hne, hq0]
      have hLq2 := hz1.mono (show q ≤ q + 2 by omega)
      have hL2 : (z.update (q - 1) 0) (q + 2) = 0 := hz1.top _ (by omega)
      have s3 : Tr (z.update (q - 1) 0 + W q 1 1 1 (M0 + 4) 0 0) 1 1
          (z.update (q - 1) 0 + W q 0 0 2 (M0 + 4) 0 0) :=
        Tr_Cp hz1.lowQ hL0 hq 0 0 1 (M0 + 4) 0 0 (Or.inl (by omega))
      have e : W q 0 0 2 (M0 + 4) 0 0 = W (q + 2) 2 (M0 + 4) 0 0 0 0 := W_shift q 2 (M0 + 4) 0 0
      rw [e] at s3
      have s4 : Tr (z.update (q - 1) 0 + W (q + 2) 2 (M0 + 4) 0 0 0 0) 1 1
          (z.update (q - 1) 0 + W (q + 2) 1 (M0 + 3) 1 0 0 0) :=
        Tr_Cp hLq2.lowQ hL2 hq2' 1 (M0 + 3) 0 0 0 0 (Or.inl (by omega))
      have s5 : Tr (z.update (q - 1) 0 + W (q + 2) 1 (M0 + 3) 1 0 0 0) 1 1
          (z.update (q - 1) 0 + W (q + 2) 0 (M0 + 2) 2 0 0 0) :=
        Tr_Cp hLq2.lowQ hL2 hq2' 0 (M0 + 2) 1 0 0 0 (Or.inl (by omega))
      have s6 : Tr (z.update (q - 1) 0 + W (q + 2) 0 (M0 + 2) 2 0 0 0) 1 0
          (z.update (q - 1) 0 + W (q + 2) 0 (M0 + 1) 1 1 0 0) :=
        Tr_Cp1 hLq2.lowQ hq2' (M0 + 1) 1 0 0 0
      have s7 : Tr (z.update (q - 1) 0 + W (q + 2) 0 (M0 + 1) 1 1 0 0) 1 0
          (z.update (q - 1) 0 + W (q + 2) 0 M0 0 2 0 0) :=
        Tr_Cp1 hLq2.lowQ hq2' M0 0 1 0 0
      exact ⟨_, 7, 5, M0, 2, hLq2, by omega,
        (((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s7,
        by omega, by omega, by omega, by omega⟩
    · -- Cases 1 and 3: the corrected entry, `C_{p+1}` before `S_{p-2}`.
      have h0 : z (q - 1) = 0 := by
        have := hz.one (q - 1)
        omega
      have hLq0 : LowQ (z + single q 1) q := hz.lowQ_add hq2 h0
      have s2 : Tr (z + single q 1 + W q 0 1 1 (M0 + 4) 0 0) 1 0
          (z + single q 1 + W q 0 0 0 (M0 + 5) 0 0) :=
        Tr_Cp1 hLq0 hq 0 0 (M0 + 4) 0 0
      have e : W q 0 0 0 (M0 + 5) 0 0 = W (q + 2) 0 (M0 + 5) 0 0 0 0 := W_shift q 0 (M0 + 5) 0 0
      rw [e] at s2
      have hI : Inert (W (q + 2) 0 (M0 + 5) 0 0 0 0) q := Inert_W (by omega) (M0 + 5) 0 0
      obtain ⟨z', k', hz', hT⟩ := cascade q hq hq2 z _ hz hI
      refine ⟨z', 1 + 1 + k', 1 + 0 + k', M0 + 5, 0, hz'.mono (by omega), by omega,
        (s1.trans s2).trans hT, by omega, by omega, by omega, by omega⟩
  · -- `K = 4`.
    have s1 : Tr (B z q 4 (M0 + 4)) 1 1 (z + single q 1 + W q 0 2 1 (M0 + 4) 0 0) :=
      Tr_Sp hq2 hq hz 2 (M0 + 4)
    by_cases h1 : z (q - 1) = 1
    · -- Case 2.
      have hq0 : z q = 0 := by
        have := hz.adj (q - 1)
        rw [show q - 1 + 1 = q by omega] at this
        omega
      have s2 := Tr_low_cons (H := W q 0 2 1 (M0 + 4) 0 0) hq2 hq hz h1 (fun i hi => W_below hi)
      rw [reshape_c0] at s2
      have hz1 : Zk (z.update (q - 1) 0) q := hz.erase (q - 1) q (fun x hx _ => hz.top x hx)
      have hL0 : (z.update (q - 1) 0) q = 0 := by
        have hne : q ≠ q - 1 := by omega
        simp [Finsupp.update_apply, hne, hq0]
      have hLq2 := hz1.mono (show q ≤ q + 2 by omega)
      have hL2 : (z.update (q - 1) 0) (q + 2) = 0 := hz1.top _ (by omega)
      have s3 : Tr (z.update (q - 1) 0 + W q 1 2 1 (M0 + 4) 0 0) 1 1
          (z.update (q - 1) 0 + W q 0 1 2 (M0 + 4) 0 0) :=
        Tr_Cp hz1.lowQ hL0 hq 0 1 1 (M0 + 4) 0 0 (Or.inl (by omega))
      have s4 : Tr (z.update (q - 1) 0 + W q 0 1 2 (M0 + 4) 0 0) 1 0
          (z.update (q - 1) 0 + W q 0 0 1 (M0 + 5) 0 0) :=
        Tr_Cp1 hz1.lowQ hq 0 1 (M0 + 4) 0 0
      have e : W q 0 0 1 (M0 + 5) 0 0 = W (q + 2) 1 (M0 + 5) 0 0 0 0 := W_shift q 1 (M0 + 5) 0 0
      rw [e] at s4
      have s5 : Tr (z.update (q - 1) 0 + W (q + 2) 1 (M0 + 5) 0 0 0 0) 1 1
          (z.update (q - 1) 0 + W (q + 2) 0 (M0 + 4) 1 0 0 0) :=
        Tr_Cp hLq2.lowQ hL2 hq2' 0 (M0 + 4) 0 0 0 0 (Or.inl (by omega))
      have s6 : Tr (z.update (q - 1) 0 + W (q + 2) 0 (M0 + 4) 1 0 0 0) 1 0
          (z.update (q - 1) 0 + W (q + 2) 0 (M0 + 3) 0 1 0 0) :=
        Tr_Cp1 hLq2.lowQ hq2' (M0 + 3) 0 0 0 0
      exact ⟨_, 6, 4, M0 + 3, 1, hLq2, by omega,
        (((((s1.trans s2).trans s3).trans s4).trans s5).trans s6),
        by omega, by omega, by omega, by omega⟩
    · have h0 : z (q - 1) = 0 := by
        have := hz.one (q - 1)
        omega
      have hLq0 : LowQ (z + single q 1) q := hz.lowQ_add hq2 h0
      have s2 : Tr (z + single q 1 + W q 0 2 1 (M0 + 4) 0 0) 1 0
          (z + single q 1 + W q 0 1 0 (M0 + 5) 0 0) :=
        Tr_Cp1 hLq0 hq 1 0 (M0 + 4) 0 0
      by_cases hzq : z q = 1
      · -- Case 3: the split `S_{p-2}` fires after `C_{p+1}`.
        by_cases hq3 : q = 2
        · subst hq3
          have s3 := Tr_low_split2 (H := W 2 0 1 0 (M0 + 5) 0 0) hz hzq (fun i hi => W_le1 hi)
            (fun x => W_quiet_adj 2 1 (M0 + 5) 0 x)
          have e : z.update 2 0 + single 1 1 + single 3 1 + W 2 0 1 0 (M0 + 5) 0 0
              = (z.update 2 0 + single 1 1) + W 2 1 1 0 (M0 + 5) 0 0 := by
            simp only [W, Nat.reduceAdd, Finsupp.single_zero]
            abel
          rw [e] at s3
          have ha : Zk (z.update 2 0) 0 := by
            refine hz.erase 2 0 ?_
            intro x hx hx2
            have hx3 : x = 1 ∨ 3 ≤ x := by omega
            rcases hx3 with rfl | hx3
            · exact h0
            · exact hz.top x (by omega)
          have hb : Zk (z.update 2 0 + single 1 1) 2 := by
            refine ha.addAt (le_refl 1) ?_ ?_ ?_ (by omega) (by omega)
            · exact ha.top 1 (by omega)
            · exact ha.zero
            · exact ha.top 2 (by omega)
          have hL0 : (z.update 2 0 + single 1 1 : Pos) 2 = 0 := by
            simp [Finsupp.add_apply, Finsupp.update_apply, Finsupp.single_apply]
          have hL2 : (z.update 2 0 + single 1 1 : Pos) (2 + 2) = 0 := hb.top _ (by omega)
          have s4 := high_m4 (q := 2) (by norm_num) (by norm_num) hb.lowQ hL0 hL2 (M0 + 3)
          exact ⟨z.update 2 0 + single 1 1, 6, 4, M0 + 3, 1, hb.mono (by omega), by omega,
            ((((s1.trans s2).trans s3).trans s4)), by omega, by omega, by omega, by omega⟩
        · have hq4 : 4 ≤ q := by omega
          have s3 := Tr_low_split (H := W q 0 1 0 (M0 + 5) 0 0) hq4 hq hz hzq
            (fun i hi => W_le1 hi) (fun x => W_quiet_adj q 1 (M0 + 5) 0 x)
          rw [reshape_c0] at s3
          have hzz : Zk (z.update q 0) (q - 2) := by
            refine hz.erase q (q - 2) ?_
            intro x hx hx2
            have hx3 : x = q - 1 ∨ q < x := by omega
            rcases hx3 with rfl | hx3
            · exact h0
            · exact hz.top x hx3
          have hInert : Inert (W (q + 2) 0 (M0 + 3) 0 1 0 0) (q - 2) :=
            Inert_W (by omega) (M0 + 3) 1 0
          obtain ⟨z', k', hz', hT⟩ := pending (q := q - 2) (by omega) (by omega) hzz hInert
            (H0 := W q 1 1 0 (M0 + 5) 0 0) (r := 3) (e := 2)
            (fun i hi => W_below (by omega))
            (fun L hL => high_m4 hq (by omega) (hL.mono (by omega)) (hL.top q (by omega))
              (hL.top (q + 2) (by omega)) (M0 + 3))
          refine ⟨z', 1 + 1 + 1 + (k' + 3), 1 + 0 + 1 + (k' + 2), M0 + 3, 1,
            hz'.mono (by omega), by omega, ((s1.trans s2).trans s3).trans hT,
            by omega, by omega, by omega, by omega⟩
      · -- Case 1.
        have hz0 : z q = 0 := by
          have := hz.one q
          omega
        have e : W q 0 1 0 (M0 + 5) 0 0 = single (q + 2) 1 + W (q + 2) 0 (M0 + 5) 0 0 0 0 :=
          W_shift1 q (M0 + 5)
        rw [e, ← add_assoc] at s2
        have hzz : Zk (z + single q 1) q :=
          hz.addAt (by omega) hz0 h0 (hz.top _ (by omega)) (le_refl _) (le_refl _)
        have hzz2 : Zk (z + single q 1 + single (q + 2) 1) (q + 2) :=
          hzz.addAt (by omega) (hzz.top _ (by omega)) (hzz.top _ (by omega))
            (hzz.top _ (by omega)) (by omega) (le_refl _)
        exact ⟨_, 2, 1, M0 + 5, 0, hzz2, by omega, s1.trans s2, by omega, by omega, by omega,
          by omega⟩

end Zeck
