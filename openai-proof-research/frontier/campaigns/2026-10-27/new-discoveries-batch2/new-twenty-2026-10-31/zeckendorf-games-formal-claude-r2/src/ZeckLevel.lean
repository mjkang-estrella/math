/-
  Part (b) of MathDB 347063: the endgame at level `p = 2`, the start phase, a whole level,
  and the bounds on a Zeckendorf low state.
-/
import ZeckExit

open Classical

set_option linter.unusedSimpArgs false

namespace Zeck

open Finsupp (single)

lemma W_shift00 (c2 c3 : ℕ) : W 0 0 0 c2 c3 0 0 = W 2 c2 c3 0 0 0 0 := by
  ext t
  simp only [W_apply]
  split_ifs <;> omega

lemma W_shift01 (c3 : ℕ) : W 0 0 1 0 c3 0 0 = single 2 1 + W 2 0 c3 0 0 0 0 := by
  ext t
  simp only [Finsupp.add_apply, Finsupp.single_apply, W_apply]
  split_ifs <;> omega

lemma W_split01 (c : ℕ) : (0 : Pos) + W 0 1 0 1 c 0 0 = single 1 1 + W 2 1 c 0 0 0 0 := by
  ext t
  simp only [Finsupp.zero_apply, zero_add, Finsupp.add_apply, Finsupp.single_apply, W_apply]
  split_ifs <;> omega

/-- The endgame at level `p = 2`. -/
theorem exit_step0 (m M0 : ℕ) (hm : m ≤ 4) :
    ∃ z' k e m' h', Zk z' 2 ∧ h' ≤ 2 ∧ Tr (B 0 0 m (M0 + 4)) k e (B z' 2 m' h') ∧
      e ≤ k ∧ k ≤ e + 2 ∧ M0 ≤ m' ∧ m' ≤ M0 + 5 := by
  have hL : LowQ (0 : Pos) 2 := (Zk_zero' 2).lowQ
  have hL0' : (0 : Pos) 2 = 0 := rfl
  have hL00 : LowQ (0 : Pos) 0 := (Zk_zero' 0).lowQ
  have hm' : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
  rcases hm' with rfl | rfl | rfl | rfl | rfl
  · have e : B 0 0 0 (M0 + 4) = B 0 2 (M0 + 4) 0 := by
      show (0 : Pos) + W 0 0 0 0 (M0 + 4) 0 0 = 0 + W 2 0 (M0 + 4) 0 0 0 0
      rw [W_shift00]
    refine ⟨0, 0, 0, M0 + 4, 0, Zk_zero' 2, by omega, ?_, by omega, by omega, by omega, by omega⟩
    rw [e]
    exact Tr.refl _
  · have e : B 0 0 1 (M0 + 4) = B (single 2 1) 2 (M0 + 4) 0 := by
      show (0 : Pos) + W 0 0 1 0 (M0 + 4) 0 0 = single 2 1 + W 2 0 (M0 + 4) 0 0 0 0
      rw [W_shift01, zero_add]
    refine ⟨single 2 1, 0, 0, M0 + 4, 0, Zk.single (by norm_num) (by norm_num), by omega, ?_,
      by omega, by omega, by omega, by omega⟩
    rw [e]
    exact Tr.refl _
  · have s1 : Tr (B 0 0 2 (M0 + 4)) 1 1 (0 + W 0 1 0 1 (M0 + 4) 0 0) := Tr_S2 0 (M0 + 4)
    rw [W_split01] at s1
    have hZ : Zk (single 1 1 : Pos) 2 := Zk.single (by norm_num) (by norm_num)
    have hL1 := hZ.lowQ
    have hL10 : (single 1 1 : Pos) 2 = 0 := by simp [Finsupp.single_apply]
    have s2 : Tr (single 1 1 + W 2 1 (M0 + 4) 0 0 0 0) 1 1 (single 1 1 + W 2 0 (M0 + 3) 1 0 0 0) :=
      Tr_Cp hL1 hL10 (by norm_num) 0 (M0 + 3) 0 0 0 0 (Or.inl (by norm_num))
    have s3 : Tr (single 1 1 + W 2 0 (M0 + 3) 1 0 0 0) 1 0 (single 1 1 + W 2 0 (M0 + 2) 0 1 0 0) :=
      Tr_Cp1 hL1 (by norm_num) (M0 + 2) 0 0 0 0
    exact ⟨single 1 1, 3, 2, M0 + 2, 1, hZ, by omega, ((s1.trans s2).trans s3), by omega, by omega,
      by omega, by omega⟩
  · have s1 : Tr (B 0 0 3 (M0 + 4)) 1 1 (0 + W 0 1 1 1 (M0 + 4) 0 0) := Tr_S2 1 (M0 + 4)
    have s2 : Tr ((0 : Pos) + W 0 1 1 1 (M0 + 4) 0 0) 1 1 (0 + W 0 0 0 2 (M0 + 4) 0 0) :=
      Tr_Cp hL00 rfl (by norm_num) 0 0 1 (M0 + 4) 0 0 (Or.inr rfl)
    rw [W_shift00] at s2
    have s3 : Tr ((0 : Pos) + W 2 2 (M0 + 4) 0 0 0 0) 1 1 (0 + W 2 1 (M0 + 3) 1 0 0 0) :=
      Tr_Cp hL hL0' (by norm_num) 1 (M0 + 3) 0 0 0 0 (Or.inl (by norm_num))
    have s4 : Tr ((0 : Pos) + W 2 1 (M0 + 3) 1 0 0 0) 1 1 (0 + W 2 0 (M0 + 2) 2 0 0 0) :=
      Tr_Cp hL hL0' (by norm_num) 0 (M0 + 2) 1 0 0 0 (Or.inl (by norm_num))
    have s5 : Tr ((0 : Pos) + W 2 0 (M0 + 2) 2 0 0 0) 1 0 (0 + W 2 0 (M0 + 1) 1 1 0 0) :=
      Tr_Cp1 hL (by norm_num) (M0 + 1) 1 0 0 0
    have s6 : Tr ((0 : Pos) + W 2 0 (M0 + 1) 1 1 0 0) 1 0 (0 + W 2 0 M0 0 2 0 0) :=
      Tr_Cp1 hL (by norm_num) M0 0 1 0 0
    exact ⟨0, 6, 4, M0, 2, Zk_zero' 2, by omega,
      ((((s1.trans s2).trans s3).trans s4).trans s5).trans s6, by omega, by omega, by omega,
      by omega⟩
  · have s1 : Tr (B 0 0 4 (M0 + 4)) 1 1 (0 + W 0 1 2 1 (M0 + 4) 0 0) := Tr_S2 2 (M0 + 4)
    have s2 : Tr ((0 : Pos) + W 0 1 2 1 (M0 + 4) 0 0) 1 1 (0 + W 0 0 1 2 (M0 + 4) 0 0) :=
      Tr_Cp hL00 rfl (by norm_num) 0 1 1 (M0 + 4) 0 0 (Or.inr rfl)
    have s3 : Tr ((0 : Pos) + W 0 0 1 2 (M0 + 4) 0 0) 1 0 (0 + W 0 0 0 1 (M0 + 5) 0 0) :=
      Tr_Cp1 hL00 (by norm_num) 0 1 (M0 + 4) 0 0
    rw [W_shift00] at s3
    have s4 : Tr ((0 : Pos) + W 2 1 (M0 + 5) 0 0 0 0) 1 1 (0 + W 2 0 (M0 + 4) 1 0 0 0) :=
      Tr_Cp hL hL0' (by norm_num) 0 (M0 + 4) 0 0 0 0 (Or.inl (by norm_num))
    have s5 : Tr ((0 : Pos) + W 2 0 (M0 + 4) 1 0 0 0) 1 0 (0 + W 2 0 (M0 + 3) 0 1 0 0) :=
      Tr_Cp1 hL (by norm_num) (M0 + 3) 0 0 0 0
    exact ⟨0, 5, 3, M0 + 3, 1, Zk_zero' 2, by omega,
      (((s1.trans s2).trans s3).trans s4).trans s5, by omega, by omega, by omega, by omega⟩

/-- A whole level: from a pool of at least `24` chips to the next READY state. -/
theorem level_step {z : Pos} {q : ℕ} (hq : q % 2 = 0) (hz : Zk z q) (m h : ℕ) (hm : 24 ≤ m)
    (hh : h ≤ 2) :
    ∃ z' k e m' h', Zk z' (q + 2) ∧ h' ≤ 2 ∧ Tr (B z q m h) k e (B z' (q + 2) m' h') ∧
      e + m' ≤ k + 3 ∧ k ≤ e + m' + 6 := by
  by_cases hq0 : q = 0
  · subst hq0
    have hz0 : z = 0 := Zk_zero hz
    subst hz0
    obtain ⟨m1, M, K, E, hm1, hT, hKE, hhM, hbound⟩ := macro_loop0 m h
    have hM4 : 4 ≤ M := by omega
    obtain ⟨M0, rfl⟩ : ∃ M0, M = M0 + 4 := ⟨M - 4, by omega⟩
    obtain ⟨z', k, e, m', h', hz', hh', hT', h1, h2, h3, h4⟩ := exit_step0 m1 M0 hm1
    exact ⟨z', K + k, E + e, m', h', hz', hh', hT.trans hT', by omega, by omega⟩
  · have hq2 : 2 ≤ q := by omega
    obtain ⟨z1, m1, M, K, E, hz1, hm1, hT, hKE, hhM, hbound⟩ := macro_loop hq hq2 m z h hz
    have hM4 : 4 ≤ M := by omega
    obtain ⟨M0, rfl⟩ : ∃ M0, M = M0 + 4 := ⟨M - 4, by omega⟩
    obtain ⟨z', k, e, m', h', hz', hh', hT', h1, h2, h3, h4⟩ := exit_step hq hq2 hz1 m1 M0 hm1
    exact ⟨z', K + k, E + e, m', h', hz', hh', hT.trans hT', by omega, by omega⟩

/-! ### The start -/

lemma start_eq_W (n : ℕ) : start n = W 0 n 0 0 0 0 0 := by
  simp [start, W]

lemma A1_phase : ∀ (i r : ℕ), Tr (W 0 (r + 2 * i) 0 0 0 0 0) i 0 (W 0 r i 0 0 0 0) := by
  intro i
  induction i with
  | zero =>
    intro r
    have e : r + 2 * 0 = r := by ring
    rw [e]
    exact Tr.refl _
  | succ i ih =>
    intro r
    have e : r + 2 * (i + 1) = (r + 2) + 2 * i := by ring
    rw [e]
    have s1 := ih (r + 2)
    have s2 : Tr (W 0 (r + 2) i 0 0 0 0) 1 0 (W 0 r (i + 1) 0 0 0 0) := Tr_A1 r i 0 0 0 0
    exact s1.trans s2

theorem start_phase (n : ℕ) (hn : 5 ≤ n) :
    ∃ m h k e, h ≤ 2 ∧ Tr (start n) k e (B 0 0 m h) ∧ 2 * e + n ≤ 2 * k ∧ 2 * k ≤ 2 * e + n + 1 := by
  have hL : LowQ (0 : Pos) 0 := (Zk_zero' 0).lowQ
  rcases Nat.even_or_odd' n with ⟨s, rfl | rfl⟩
  · refine ⟨s, 0, s, 0, by omega, ?_, by omega, by omega⟩
    have s1 := A1_phase s 0
    rw [zero_add, ← start_eq_W] at s1
    have e : B 0 0 s 0 = W 0 0 s 0 0 0 0 := by
      show (0 : Pos) + W 0 0 s 0 0 0 0 = W 0 0 s 0 0 0 0
      rw [zero_add]
    rw [e]
    exact s1
  · obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
    have s1 := A1_phase (t + 2) 1
    rw [show 1 + 2 * (t + 2) = 2 * (t + 2) + 1 by ring, ← start_eq_W] at s1
    rw [show W 0 1 (t + 2) 0 0 0 0 = (0 : Pos) + W 0 1 (t + 2) 0 0 0 0 from (zero_add _).symm]
      at s1
    have s2 : Tr ((0 : Pos) + W 0 1 (t + 2) 0 0 0 0) 1 1 (0 + W 0 0 (t + 1) 1 0 0 0) :=
      Tr_Cp hL rfl (by norm_num) 0 (t + 1) 0 0 0 0 (Or.inr rfl)
    have s3 : Tr ((0 : Pos) + W 0 0 (t + 1) 1 0 0 0) 1 0 (0 + W 0 0 t 0 1 0 0) :=
      Tr_Cp1 hL (by norm_num) t 0 0 0 0
    exact ⟨t, 1, t + 2 + 1 + 1, 0 + 1 + 0, by omega, (s1.trans s2).trans s3, by omega, by omega⟩

/-! ### Bounds for Zeckendorf low states -/

lemma Zk.val_lt : ∀ (t : ℕ) (z : Pos), Zk z t → val z < F (t + 1) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro z hz
    by_cases hzero : z t = 0
    · rcases Nat.eq_zero_or_pos t with rfl | ht
      · rw [Zk_zero hz]
        simp [val]
      · have hz' : Zk z (t - 1) := by
          refine ⟨hz.one, hz.adj, hz.zero, ?_⟩
          intro i hi
          by_cases hit : i = t
          · subst hit; exact hzero
          · exact hz.top i (by omega)
        have h1 := ih (t - 1) (by omega) z hz'
        have h2 : F (t - 1 + 1) ≤ F (t + 1) := F_mono (by omega)
        omega
    · have h1 : z t = 1 := by
        have := hz.one t
        omega
      have hzt : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with rfl | ht
        · exact absurd hz.zero hzero
        · exact ht
      have hadj : z (t - 1) = 0 := by
        have := hz.adj (t - 1)
        rw [show t - 1 + 1 = t by omega] at this
        omega
      have hz1 : Zk (z.update t 0) (t - 2) := by
        refine hz.erase t (t - 2) ?_
        intro x hx hxt
        have hx3 : x = t - 1 ∨ t < x := by omega
        rcases hx3 with rfl | hx3
        · exact hadj
        · exact hz.top x hx3
      have h2 := ih (t - 2) (by omega) _ hz1
      have hval : val z = val (z.update t 0) + F t := by
        conv_lhs => rw [decompose_at z t h1]
        rw [val_add, val_single, one_mul]
      have hrec : F (t + 1) = F t + F (t - 1) := F_rec hzt
      have hle : F (t - 2 + 1) ≤ F (t - 1) := by
        rcases Nat.lt_or_ge t 2 with ht2 | ht2
        · have e : t = 1 := by omega
          subst e
          simp
        · have e : t - 2 + 1 = t - 1 := by omega
          rw [e]
      omega

lemma Zk.chips_le : ∀ (t : ℕ) (z : Pos), Zk z t → chips z ≤ t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro z hz
    by_cases hzero : z t = 0
    · rcases Nat.eq_zero_or_pos t with rfl | ht
      · rw [Zk_zero hz]
        simp [chips]
      · have hz' : Zk z (t - 1) := by
          refine ⟨hz.one, hz.adj, hz.zero, ?_⟩
          intro i hi
          by_cases hit : i = t
          · subst hit; exact hzero
          · exact hz.top i (by omega)
        have h1 := ih (t - 1) (by omega) z hz'
        omega
    · have h1 : z t = 1 := by
        have := hz.one t
        omega
      have hzt : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with rfl | ht
        · exact absurd hz.zero hzero
        · exact ht
      have hadj : z (t - 1) = 0 := by
        have := hz.adj (t - 1)
        rw [show t - 1 + 1 = t by omega] at this
        omega
      have hz1 : Zk (z.update t 0) (t - 2) := by
        refine hz.erase t (t - 2) ?_
        intro x hx hxt
        have hx3 : x = t - 1 ∨ t < x := by omega
        rcases hx3 with rfl | hx3
        · exact hadj
        · exact hz.top x hx3
      have h2 := ih (t - 2) (by omega) _ hz1
      have hval : chips z = chips (z.update t 0) + 1 := by
        conv_lhs => rw [decompose_at z t h1]
        rw [chips_add, chips_single]
      omega

/-- The value in a READY state is the conserved game value. -/
lemma val_B (z : Pos) (q m h : ℕ) : val (B z q m h) = val z + m * F (q + 2) + h * F (q + 4) := by
  unfold B
  rw [val_add, val_W]
  omega

lemma chips_B (z : Pos) (q m h : ℕ) : chips (B z q m h) = chips z + m + h := by
  unfold B
  rw [chips_add, chips_W]
  omega

lemma F_add_two_le (q : ℕ) : F (q + 4) ≤ 3 * F (q + 2) := by
  have h1 : F (q + 4) = F (q + 3) + F (q + 2) := by
    have := F_rec (i := q + 3) (by omega)
    simpa using this
  have h2 : F (q + 3) = F (q + 2) + F (q + 1) := by
    have := F_rec (i := q + 2) (by omega)
    simpa using this
  have h3 : F (q + 1) ≤ F (q + 2) := F_mono (by omega)
  omega

end Zeck
