/-
  Part (b) of MathDB 347063: the READY state and the macro step of the rotation.

  `B z q m h` has a Zeckendorf low state `z` of top index at most `q`, a pool of `m` chips at
  index `p = q + 2` and `h` chips at `p + 2`.  Every macro step sends the low value
  `L = val z` to the rotation `L + F_{p-2} mod F_{p-1}`, the counter records it exactly,
  and the output pile records the odd combines.
-/
import ZeckLow

open Classical

set_option linter.unusedSimpArgs false

namespace Zeck

open Finsupp (single)

/-- The READY state at level `p = q + 2`. -/
noncomputable def B (z : Pos) (q m h : ℕ) : Pos := z + W q 0 m 0 h 0 0

lemma reshape_c0 (L : Pos) (q c1 c2 c3 c4 c5 : ℕ) :
    L + single (q + 1) 1 + W q 0 c1 c2 c3 c4 c5 = L + W q 1 c1 c2 c3 c4 c5 := by
  simp only [W, Finsupp.single_zero]
  abel

lemma W_le1 {q c1 c2 c3 c4 c5 i : ℕ} (hi : i ≤ q + 1) : W q 0 c1 c2 c3 c4 c5 i = 0 := by
  rw [W_apply]
  split_ifs <;> omega

lemma Zk_zero' (t : ℕ) : Zk (0 : Pos) t :=
  ⟨fun _ => by simp, fun _ => by simp, by simp, fun _ _ => by simp⟩

lemma Zk_zero {z : Pos} (h : Zk z 0) : z = 0 := by
  ext i
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simpa using h.zero
  · simpa using h.top i hi

lemma Zk.single {i t : ℕ} (hi : 1 ≤ i) (ht : i ≤ t) : Zk (single i 1 : Pos) t := by
  have h := (Zk_zero' t).addAt (i := i) (t' := t) hi (by simp) (by simp) (by simp) (le_refl _) ht
  simpa using h

lemma high_m5 {L : Pos} {q : ℕ} (hq : q % 2 = 0) (hq1 : 1 ≤ q) (hL : LowQ L q) (hL0 : L q = 0)
    (m h : ℕ) :
    Tr (L + W q 1 (m + 2) 0 h 0 0) 2 1 (L + W q 0 m 0 (h + 1) 0 0) := by
  have s1 : Tr (L + W q 1 (m + 2) 0 h 0 0) 1 1 (L + W q 0 (m + 1) 1 h 0 0) :=
    Tr_Cp hL hL0 hq 0 (m + 1) 0 h 0 0 (Or.inl hq1)
  have s2 : Tr (L + W q 0 (m + 1) 1 h 0 0) 1 0 (L + W q 0 m 0 (h + 1) 0 0) :=
    Tr_Cp1 hL hq m 0 h 0 0
  exact s1.trans s2

/-- The macro step at level `p = q + 2 ≥ 4`. -/
theorem macro_step {z : Pos} {q : ℕ} (hq : q % 2 = 0) (hq2 : 2 ≤ q) (hz : Zk z q) (m h : ℕ) :
    ∃ z' k e m' h', Zk z' q ∧ Tr (B z q (m + 5) h) k e (B z' q m' h') ∧
      ((m' = m + 2 ∧ h' = h + 1 ∧ k = e + 1) ∨ (m' = m ∧ h' = h + 2 ∧ k = e + 2)) := by
  have s1 : Tr (B z q (m + 5) h) 1 1 (z + single q 1 + W q 0 (m + 3) 1 h 0 0) :=
    Tr_Sp hq2 hq hz (m + 3) h
  by_cases h1 : z (q - 1) = 1
  · -- Case 2: `C_{p-2}` creates the chip at `p-1`.
    have hq0 : z q = 0 := by
      have := hz.adj (q - 1)
      rw [show q - 1 + 1 = q by omega] at this
      omega
    have hz1 : Zk (z.update (q - 1) 0) q := hz.erase (q - 1) q (fun x hx _ => hz.top x hx)
    have hL0 : (z.update (q - 1) 0) q = 0 := by
      have hne : q ≠ q - 1 := by omega
      simp [Finsupp.update_apply, hne, hq0]
    have s2 := Tr_low_cons (H := W q 0 (m + 3) 1 h 0 0) hq2 hq hz h1 (fun i hi => W_below hi)
    rw [reshape_c0] at s2
    have s3 : Tr (z.update (q - 1) 0 + W q 1 (m + 3) 1 h 0 0) 1 1
        (z.update (q - 1) 0 + W q 0 (m + 2) 2 h 0 0) :=
      Tr_Cp hz1.lowQ hL0 hq 0 (m + 2) 1 h 0 0 (Or.inl (by omega))
    have s4 : Tr (z.update (q - 1) 0 + W q 0 (m + 2) 2 h 0 0) 1 0
        (z.update (q - 1) 0 + W q 0 (m + 1) 1 (h + 1) 0 0) :=
      Tr_Cp1 hz1.lowQ hq (m + 1) 1 h 0 0
    have s5 : Tr (z.update (q - 1) 0 + W q 0 (m + 1) 1 (h + 1) 0 0) 1 0
        (z.update (q - 1) 0 + W q 0 m 0 (h + 2) 0 0) :=
      Tr_Cp1 hz1.lowQ hq m 0 (h + 1) 0 0
    exact ⟨z.update (q - 1) 0, 5, 3, m, h + 2, hz1, ((((s1.trans s2).trans s3).trans s4).trans s5),
      Or.inr ⟨rfl, rfl, rfl⟩⟩
  · have h0 : z (q - 1) = 0 := by
      have := hz.one (q - 1)
      omega
    have hLq : LowQ (z + single q 1) q := hz.lowQ_add hq2 h0
    have s2 : Tr (z + single q 1 + W q 0 (m + 3) 1 h 0 0) 1 0
        (z + single q 1 + W q 0 (m + 2) 0 (h + 1) 0 0) :=
      Tr_Cp1 hLq hq (m + 2) 0 h 0 0
    by_cases hzq : z q = 1
    · -- Case 3: a split `S_{p-2}` after the output combine.
      by_cases hq3 : q = 2
      · subst hq3
        have s3 := Tr_low_split2 (H := W 2 0 (m + 2) 0 (h + 1) 0 0) hz hzq (fun i hi => W_le1 hi)
          (fun x => W_quiet_adj 2 (m + 2) (h + 1) 0 x)
        have e : z.update 2 0 + single 1 1 + single 3 1 + W 2 0 (m + 2) 0 (h + 1) 0 0
            = (z.update 2 0 + single 1 1) + W 2 1 (m + 2) 0 (h + 1) 0 0 := by
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
        have s4 := high_m5 (q := 2) (by norm_num) (by norm_num) hb.lowQ hL0 m (h + 1)
        exact ⟨z.update 2 0 + single 1 1, 5, 3, m, h + 2, hb,
          (((s1.trans s2).trans s3).trans s4), Or.inr ⟨rfl, rfl, rfl⟩⟩
      · have hq4 : 4 ≤ q := by omega
        have s3 := Tr_low_split (H := W q 0 (m + 2) 0 (h + 1) 0 0) hq4 hq hz hzq
          (fun i hi => W_le1 hi) (fun x => W_quiet_adj q (m + 2) (h + 1) 0 x)
        rw [reshape_c0] at s3
        have hzz : Zk (z.update q 0) (q - 2) := by
          refine hz.erase q (q - 2) ?_
          intro x hx hx2
          have hx3 : x = q - 1 ∨ q < x := by omega
          rcases hx3 with rfl | hx3
          · exact h0
          · exact hz.top x hx3
        have hInert : Inert (W q 0 m 0 (h + 2) 0 0) (q - 2) := Inert_W (by omega) m (h + 2) 0
        obtain ⟨z', k', hz', hT⟩ := pending (q := q - 2) (by omega) (by omega) hzz hInert
          (H0 := W q 1 (m + 2) 0 (h + 1) 0 0) (r := 2) (e := 1)
          (fun i hi => W_below (by omega))
          (fun L hL => high_m5 hq (by omega) (hL.mono (by omega)) (hL.top q (by omega)) m (h + 1))
        have hzq' : Zk z' q := hz'.mono (by omega)
        refine ⟨z', 1 + 1 + 1 + (k' + 2), 1 + 0 + 1 + (k' + 1), m, h + 2, hzq',
          ((s1.trans s2).trans s3).trans hT, Or.inr ⟨rfl, rfl, by omega⟩⟩
    · -- Case 1: no low move at all.
      have hz0 : z q = 0 := by
        have := hz.one q
        omega
      have hzz : Zk (z + single q 1) q :=
        hz.addAt (by omega) hz0 h0 (hz.top _ (by omega)) (le_refl _) (le_refl _)
      exact ⟨z + single q 1, 2, 1, m + 2, h + 1, hzz, s1.trans s2, Or.inl ⟨rfl, rfl, rfl⟩⟩

/-- The macro step at level `p = 2`, where the low state is empty. -/
theorem macro_step0 (m h : ℕ) : Tr (B 0 0 (m + 5) h) 4 2 (B 0 0 m (h + 2)) := by
  have hL : LowQ (0 : Pos) 0 := (Zk_zero' 0).lowQ
  have hL0 : (0 : Pos) 0 = 0 := rfl
  have s1 : Tr (B 0 0 (m + 5) h) 1 1 (0 + W 0 1 (m + 3) 1 h 0 0) := Tr_S2 (m + 3) h
  have s2 : Tr ((0 : Pos) + W 0 1 (m + 3) 1 h 0 0) 1 1 (0 + W 0 0 (m + 2) 2 h 0 0) :=
    Tr_Cp hL hL0 (by norm_num) 0 (m + 2) 1 h 0 0 (Or.inr rfl)
  have s3 : Tr ((0 : Pos) + W 0 0 (m + 2) 2 h 0 0) 1 0 (0 + W 0 0 (m + 1) 1 (h + 1) 0 0) :=
    Tr_Cp1 hL (by norm_num) (m + 1) 1 h 0 0
  have s4 : Tr ((0 : Pos) + W 0 0 (m + 1) 1 (h + 1) 0 0) 1 0 (0 + W 0 0 m 0 (h + 2) 0 0) :=
    Tr_Cp1 hL (by norm_num) m 0 (h + 1) 0 0
  exact (((s1.trans s2).trans s3).trans s4)

/-- The whole pool of level `p = q + 2 ≥ 4` is consumed by macro steps. -/
theorem macro_loop {q : ℕ} (hq : q % 2 = 0) (hq2 : 2 ≤ q) :
    ∀ (m : ℕ) (z : Pos) (h : ℕ), Zk z q →
      ∃ z1 m1 M K E, Zk z1 q ∧ m1 ≤ 4 ∧ Tr (B z q m h) K E (B z1 q m1 M) ∧
        K = E + (M - h) ∧ h ≤ M ∧ m ≤ m1 + 5 * (M - h) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro z h hz
    by_cases hm : m ≤ 4
    · exact ⟨z, m, h, 0, 0, hz, hm, Tr.refl _, by omega, le_refl _, by omega⟩
    · obtain ⟨m0, rfl⟩ : ∃ m0, m = m0 + 5 := ⟨m - 5, by omega⟩
      obtain ⟨z', k, e, m', h', hz', hT, hcase⟩ := macro_step hq hq2 hz m0 h
      have hm' : m' < m0 + 5 := by
        rcases hcase with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ <;> omega
      obtain ⟨z1, m1, M, K, E, hz1, hm1, hT', hKE, hhM, hbound⟩ := ih m' hm' z' h' hz'
      refine ⟨z1, m1, M, k + K, e + E, hz1, hm1, hT.trans hT', ?_, ?_, ?_⟩
      · rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> omega
      · rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> omega
      · rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> omega

/-- The loop at level `p = 2`. -/
theorem macro_loop0 : ∀ (m h : ℕ),
    ∃ m1 M K E, m1 ≤ 4 ∧ Tr (B 0 0 m h) K E (B 0 0 m1 M) ∧
      K = E + (M - h) ∧ h ≤ M ∧ m ≤ m1 + 5 * (M - h) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro h
    by_cases hm : m ≤ 4
    · exact ⟨m, h, 0, 0, hm, Tr.refl _, by omega, le_refl _, by omega⟩
    · obtain ⟨m0, rfl⟩ : ∃ m0, m = m0 + 5 := ⟨m - 5, by omega⟩
      obtain ⟨m1, M, K, E, hm1, hT', hKE, hhM, hbound⟩ := ih m0 (by omega) (h + 2)
      refine ⟨m1, M, 4 + K, 2 + E, hm1, (macro_step0 m0 h).trans hT', by omega, by omega, by omega⟩

end Zeck
