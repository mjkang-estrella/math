/-
  Part (b) of MathDB 347063: the rotation of the low state and the chip balance of a cycle.

  These statements are not used by the endpoint theorems (the counter `D` replaces them),
  but they are what the proof plan asked for: a macro step acts on the low value `L = val z`
  as the rotation `L ↦ L + F_{p-2} mod F_{p-1}`, a full cycle of `F_{p-1}` macros returns the
  low state, and a cycle consists of exactly `F_{p+2} - 1` moves, of which exactly `F_p - 1`
  are splits.  Here `q = p - 2`.
-/
import ZeckLevel

open Classical

set_option linter.unusedSimpArgs false

namespace Zeck

open Finsupp (single)

lemma F_add_four (q : ℕ) : F (q + 4) = 2 * F (q + 2) + F (q + 1) := by
  have h1 : F (q + 4) = F (q + 3) + F (q + 2) := by
    have := F_rec (i := q + 3) (by omega)
    simpa using this
  have h2 : F (q + 3) = F (q + 2) + F (q + 1) := by
    have := F_rec (i := q + 2) (by omega)
    simpa using this
  omega

lemma F_add_two (q : ℕ) : F (q + 2) = F (q + 1) + F q := by
  have := F_rec (i := q + 1) (by omega)
  simpa using this

/-- A macro step as a rotation of the low value. -/
theorem macro_rot {z : Pos} {q : ℕ} (hq : q % 2 = 0) (hq2 : 2 ≤ q) (hz : Zk z q) (m h : ℕ) :
    ∃ z' k e m' h', Zk z' q ∧ Tr (B z q (m + 5) h) k e (B z' q m' h') ∧
      ((m' = m + 2 ∧ h' = h + 1 ∧ k = e + 1 ∧ val z' = val z + F q) ∨
       (m' = m ∧ h' = h + 2 ∧ k = e + 2 ∧ val z' + F (q + 1) = val z + F q)) := by
  obtain ⟨z', k, e, m', h', hz', hT, hc⟩ := macro_step hq hq2 hz m h
  refine ⟨z', k, e, m', h', hz', hT, ?_⟩
  have hval := hT.st.val_eq
  rw [val_B, val_B] at hval
  have hF4 := F_add_four q
  have hF2 := F_add_two q
  rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · refine Or.inl ⟨rfl, rfl, rfl, ?_⟩
    simp only [Nat.add_mul] at hval
    omega
  · refine Or.inr ⟨rfl, rfl, rfl, ?_⟩
    simp only [Nat.add_mul] at hval
    omega

/-- The rotation in the mod form of the review: a macro step sends `L` to
`(L + F_{p-2}) % F_{p-1}`. -/
theorem macro_rotation {z : Pos} {q : ℕ} (hq : q % 2 = 0) (hq2 : 2 ≤ q) (hz : Zk z q) (m h : ℕ) :
    ∃ z' k e m' h', Zk z' q ∧ Tr (B z q (m + 5) h) k e (B z' q m' h') ∧
      val z' = (val z + F q) % F (q + 1) := by
  obtain ⟨z', k, e, m', h', hz', hT, hc⟩ := macro_rot hq hq2 hz m h
  refine ⟨z', k, e, m', h', hz', hT, ?_⟩
  have hlt := hz'.val_lt _ _
  rcases hc with ⟨_, _, _, hv⟩ | ⟨_, _, _, hv⟩
  · rw [← hv]
    exact (Nat.mod_eq_of_lt hlt).symm
  · have e1 : val z + F q = val z' + F (q + 1) := hv.symm
    rw [e1, Nat.add_mod_right]
    exact (Nat.mod_eq_of_lt hlt).symm

/-- Iterating the macro step. -/
theorem macro_iter {q : ℕ} (hq : q % 2 = 0) (hq2 : 2 ≤ q) :
    ∀ (t : ℕ) (z : Pos) (m h : ℕ), Zk z q → 5 * t ≤ m →
      ∃ z' k e m' h' w, Zk z' q ∧ Tr (B z q m h) k e (B z' q m' h') ∧ w ≤ t ∧
        m' + 3 * (t - w) + 5 * w = m ∧ h' = h + (t - w) + 2 * w ∧ k = e + (t - w) + 2 * w ∧
        val z' + w * F (q + 1) = val z + t * F q := by
  intro t
  induction t with
  | zero =>
    intro z m h hz _
    exact ⟨z, 0, 0, m, h, 0, hz, Tr.refl _, le_refl _, by omega, by omega, by omega, by simp⟩
  | succ t ih =>
    intro z m h hz hm
    obtain ⟨m0, rfl⟩ : ∃ m0, m = m0 + 5 := ⟨m - 5, by omega⟩
    obtain ⟨z1, k1, e1, m1, h1, hz1, hT1, hc⟩ := macro_rot hq hq2 hz m0 h
    have hm1 : 5 * t ≤ m1 := by
      rcases hc with ⟨rfl, _, _, _⟩ | ⟨rfl, _, _, _⟩ <;> omega
    obtain ⟨z', k2, e2, m', h', w, hz', hT2, hw, hmm, hhh, hkk, hvv⟩ := ih z1 m1 h1 hz1 hm1
    have htF : (t + 1) * F q = t * F q + F q := by ring
    rcases hc with ⟨rfl, rfl, rfl, hv⟩ | ⟨rfl, rfl, rfl, hv⟩
    · refine ⟨z', e1 + 1 + k2, e1 + e2, m', h', w, hz', hT1.trans hT2, by omega, by omega,
        by omega, by omega, ?_⟩
      rw [htF]
      omega
    · refine ⟨z', e1 + 2 + k2, e1 + e2, m', h', w + 1, hz', hT1.trans hT2, by omega, by omega,
        by omega, by omega, ?_⟩
      have hwF : (w + 1) * F (q + 1) = w * F (q + 1) + F (q + 1) := by ring
      rw [htF, hwF]
      omega

/-- Zeckendorf uniqueness for low states. -/
theorem Zk.eq_of_val : ∀ (t : ℕ) (a b : Pos), Zk a t → Zk b t → val a = val b → a = b := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro a b ha hb hv
    have lowZ : ∀ (c : Pos), Zk c t → c t = 0 → Zk c (t - 1) := by
      intro c hc h0
      refine ⟨hc.one, hc.adj, hc.zero, ?_⟩
      intro i hi
      by_cases hit : i = t
      · subst hit; exact h0
      · exact hc.top i (by omega)
    have top1 : ∀ (c : Pos), Zk c t → c t = 1 → 1 ≤ t := by
      intro c hc h1
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · rw [hc.zero] at h1
        omega
      · exact ht
    have erase : ∀ (c : Pos), Zk c t → c t = 1 → Zk (c.update t 0) (t - 2) := by
      intro c hc h1
      have ht := top1 c hc h1
      have hadj : c (t - 1) = 0 := by
        have := hc.adj (t - 1)
        rw [show t - 1 + 1 = t by omega] at this
        omega
      refine hc.erase t (t - 2) ?_
      intro x hx hxt
      have hx3 : x = t - 1 ∨ t < x := by omega
      rcases hx3 with rfl | hx3
      · exact hadj
      · exact hc.top x hx3
    have valtop : ∀ (c : Pos), c t = 1 → val c = val (c.update t 0) + F t := by
      intro c h1
      conv_lhs => rw [decompose_at c t h1]
      rw [val_add, val_single, one_mul]
    have hnocross : ∀ (c d : Pos), Zk c t → Zk d t → c t = 0 → d t = 1 → val c ≠ val d := by
      intro c d hc hd h0 h1 he
      have ht := top1 d hd h1
      have h3 := (lowZ c hc h0).val_lt (t - 1) c
      have h4 := valtop d h1
      have e : t - 1 + 1 = t := by omega
      rw [e] at h3
      omega
    by_cases ha0 : a t = 0
    · by_cases hb0 : b t = 0
      · rcases Nat.eq_zero_or_pos t with rfl | ht
        · rw [Zk_zero ha, Zk_zero hb]
        · exact ih (t - 1) (by omega) a b (lowZ a ha ha0) (lowZ b hb hb0) hv
      · have hb1 : b t = 1 := by
          have := hb.one t
          omega
        exact absurd hv (hnocross a b ha hb ha0 hb1)
    · have ha1 : a t = 1 := by
        have := ha.one t
        omega
      by_cases hb0 : b t = 0
      · exact absurd hv.symm (hnocross b a hb ha hb0 ha1)
      · have hb1 : b t = 1 := by
          have := hb.one t
          omega
        have ht := top1 a ha ha1
        have hE := ih (t - 2) (by omega) _ _ (erase a ha ha1) (erase b hb hb1) (by
          have h1 := valtop a ha1
          have h2 := valtop b hb1
          omega)
        calc a = a.update t 0 + Finsupp.single t 1 := decompose_at a t ha1
          _ = b.update t 0 + Finsupp.single t 1 := by rw [hE]
          _ = b := (decompose_at b t hb1).symm

/-! ### Counting the splits -/

/-- The chosen Combine Smallest move at `a` is a split. -/
def splitMoveAt (a : Pos) : Prop :=
  ¬ legalA1 a ∧ smallestCons a = none ∧ ∃ i, legalSplit a i

/-- The number of split moves among the first `k` moves from `a`. -/
noncomputable def splitCount (a : Pos) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range k, (if splitMoveAt (run stepCS a j) then 1 else 0)

lemma chips_step_split {a : Pos} (h : splitMoveAt a) : chips (stepCS a) = chips a := by
  obtain ⟨hA, hco, hex⟩ := h
  cases hsp : smallestSplit a with
  | none => exact absurd hex ((smallestSplit_none_iff a).1 hsp)
  | some i =>
    have hs : stepCS a = doSplit a i := by
      unfold stepCS
      simp [hA, hco, hsp]
    rw [hs]
    exact chips_doSplit a i (smallestSplit_some_spec a hsp).1

lemma chips_step_nonsplit {a : Pos} (hm : hasMove a) (h : ¬ splitMoveAt a) :
    chips (stepCS a) + 1 = chips a := by
  by_cases hA : legalA1 a
  · rw [stepCS_A1 a hA]
    exact chips_doA1 a hA
  · cases hco : smallestCons a with
    | some i =>
      have hl := (smallestCons_some_spec a hco).1
      have hs : stepCS a = doCons a i := by
        unfold stepCS
        simp [hA, hco]
      rw [hs]
      exact chips_doCons a i hl
    | none =>
      exfalso
      rcases hm with ha | ⟨i, hi⟩ | hs
      · exact hA ha
      · exact (smallestCons_none_iff a).1 hco ⟨i, hi⟩
      · exact h ⟨hA, hco, hs⟩

/-- Over any Combine Smallest run, chips lost plus splits equals moves. -/
theorem Steps_chips {a b : Pos} {k : ℕ} (h : Steps a k b) :
    chips a + splitCount a k = chips b + k := by
  induction h with
  | refl a => simp [splitCount]
  | @head a k c hm _ ih =>
    have hsum : splitCount a (k + 1) = splitCount (stepCS a) k
        + (if splitMoveAt a then 1 else 0) := by
      unfold splitCount
      rw [Finset.sum_range_succ']
      congr 1
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [run_succ']
    rw [hsum]
    by_cases hs : splitMoveAt a
    · have h1 := chips_step_split hs
      simp [hs]
      omega
    · have h1 := chips_step_nonsplit hm hs
      simp [hs]
      omega

/-! ### The cycle -/

lemma fib_even_identity (j : ℕ) :
    F (2 * j + 1) * F (2 * j + 1) + 1 = F (2 * j) * F (2 * j) + F (2 * j) * F (2 * j + 1) := by
  induction j with
  | zero => decide
  | succ j ih =>
    have e1 : 2 * (j + 1) = 2 * j + 2 := by ring
    have e2 : 2 * (j + 1) + 1 = 2 * j + 3 := by ring
    rw [e2, e1]
    have h1 : F (2 * j + 2) = F (2 * j + 1) + F (2 * j) := F_add_two (2 * j)
    have h2 : F (2 * j + 3) = F (2 * j + 2) + F (2 * j + 1) := F_add_two (2 * j + 1)
    rw [h2, h1]
    nlinarith

/-- The Cassini-type identity behind the moves per cycle. -/
lemma cassini_even {q : ℕ} (hq : q % 2 = 0) : F (q + 2) * F (q + 2) + 1 = F q * F (q + 4) := by
  obtain ⟨j, rfl⟩ : ∃ j, q = 2 * j := ⟨q / 2, by omega⟩
  have h := fib_even_identity j
  have h1 : F (2 * j + 2) = F (2 * j + 1) + F (2 * j) := F_add_two (2 * j)
  have h2 : F (2 * j + 3) = F (2 * j + 2) + F (2 * j + 1) := F_add_two (2 * j + 1)
  have h4 : F (2 * j + 4) = 2 * F (2 * j + 2) + F (2 * j + 1) := F_add_four (2 * j)
  rw [h4, h1]
  nlinarith

/-- One full rotation cycle of the level `p = q + 2 ≥ 4`: the low state returns, the pool
loses `F_{p+2}`, the output pile gains `F_p`, the cycle has `F_{p+2} - 1` moves, of which
exactly `F_p - 1` are splits. -/
theorem rotation_cycle {q : ℕ} (hq : q % 2 = 0) (hq2 : 2 ≤ q) {z : Pos} (hz : Zk z q) (m h : ℕ)
    (hm : 5 * F (q + 1) ≤ m) :
    ∃ k e, Tr (B z q m h) k e (B z q (m - F (q + 4)) (h + F (q + 2))) ∧
      k + 1 = F (q + 4) ∧ splitCount (B z q m h) k + 1 = F (q + 2) := by
  obtain ⟨z', k, e, m', h', w, hz', hT, hw, hmm, hhh, hkk, hvv⟩ :=
    macro_iter hq hq2 (F (q + 1)) z m h hz hm
  have hc : 0 < F (q + 1) := F_pos _
  have hlt1 : val z' < F (q + 1) := hz'.val_lt _ _
  have hlt2 : val z < F (q + 1) := hz.val_lt _ _
  have hmod : val z' % F (q + 1) = val z % F (q + 1) := by
    have h1 := congrArg (· % F (q + 1)) hvv
    simp only [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_left] at h1
    exact h1
  have hval : val z' = val z := by
    rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hmod
    exact hmod
  have hzz : z' = z := Zk.eq_of_val q z' z hz' hz hval
  subst hzz
  have hwF : w = F q := by
    have h1 : w * F (q + 1) = F q * F (q + 1) := by
      have h2 : F (q + 1) * F q = F q * F (q + 1) := by ring
      omega
    exact Nat.eq_of_mul_eq_mul_right hc h1
  subst hwF
  have hF4 := F_add_four q
  have hF2 := F_add_two q
  have hFq : F q ≤ F (q + 1) := F_mono (by omega)
  have hm' : m' = m - F (q + 4) := by omega
  have hh' : h' = h + F (q + 2) := by omega
  have hmF4 : F (q + 4) ≤ m := by omega
  subst hm'
  subst hh'
  -- the counter
  have hD := hT.dv
  have ha : d (q + 2) + 1 = F q := by
    have := d_even (i := q + 2) (by omega) (by omega)
    simpa [F] using this
  have hb : d (q + 4) + 1 = F (q + 2) := by
    have := d_even (i := q + 4) (by omega) (by omega)
    simpa [F] using this
  have hcass := cassini_even hq
  have hDz : D (B z' q (m - F (q + 4)) (h + F (q + 2))) =
      D z' + (m - F (q + 4)) * d (q + 2) + (h + F (q + 2)) * d (q + 4) := by
    unfold B
    rw [D_add, D_W]
    ring
  have hDz2 : D (B z' q m h) = D z' + m * d (q + 2) + h * d (q + 4) := by
    unfold B
    rw [D_add, D_W]
    ring
  rw [hDz, hDz2] at hD
  have hpm : (m - F (q + 4)) * d (q + 2) + F (q + 4) * d (q + 2) = m * d (q + 2) := by
    rw [← Nat.add_mul]
    congr 1
    omega
  have h2b : (h + F (q + 2)) * d (q + 4) = h * d (q + 4) + F (q + 2) * d (q + 4) := by ring
  have hP : F (q + 2) * d (q + 4) + F (q + 2) = F (q + 2) * F (q + 2) := by
    rw [← hb]
    ring
  have hQ : F (q + 4) * d (q + 2) + F (q + 4) = F q * F (q + 4) := by
    rw [← ha]
    ring
  have he : e + F (q + 4) * d (q + 2) = F (q + 2) * d (q + 4) := by omega
  have hk : k + 1 = F (q + 4) := by omega
  refine ⟨k, e, hT, hk, ?_⟩
  have hchips := Steps_chips hT.st
  rw [chips_B, chips_B] at hchips
  omega

end Zeck
