import Sem5Sink
namespace ChanLevine.Sem5
variable {n : ℕ} [NeZero n]

/-- A Boolean path without a right-left transition is a left prefix. -/
theorem bool_prefix (q : ℕ → Bool) (N : ℕ)
    (hq : ∀ k, 1 ≤ k → k < N → q k = true → q (k+1) = true) :
    ∃ i, i ≤ N ∧ ∀ k, 1 ≤ k → k ≤ N → q k = if k ≤ i then false else true := by
  induction N with
  | zero => exact ⟨0, by omega, by intros; omega⟩
  | succ N ih =>
    obtain ⟨i, hi, hpat⟩ := ih (fun k hk hkn => hq k hk (by omega))
    cases he : q (N+1) with
    | true =>
      refine ⟨i, by omega, ?_⟩
      intro k hk hkn
      by_cases h : k ≤ N
      · exact hpat k hk h
      · have : k = N+1 := by omega
        subst k
        simp [he, show ¬ N+1 ≤ i by omega]
    | false =>
      have hie : i = N := by
        by_contra hh
        have hN : 1 ≤ N := by omega
        have hqt : q N = true := by simpa [show ¬ N ≤ i by omega] using hpat N hN (by omega)
        have := hq N hN (by omega) hqt
        simp [he] at this
      refine ⟨N+1, by omega, ?_⟩
      intro k hk hkn
      by_cases h : k ≤ N
      · simpa [hie, h, hkn] using hpat k hk h
      · have : k = N+1 := by omega
        subst k
        simp [he]

/-- Recurrent sink states with rotor zero right are exactly the canonical states. -/
theorem sink_classification (hn : 3 ≤ n) (d : Config n) (hd : NatRecurrent d)
    (hx : ∀ v, v ≠ 0 → d.x v = 0) (hq : d.q 0 = true) :
    d = canonical (chipLevel d) (chipWeight d) := by
  have ht := Sem3.recurrent_cycleTest hn hd
  have hcast : ∀ k : ℕ, k < n → (k : ZMod n).val = k := by
    intro k hk
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt hk]
  have hpath : ∀ k, 1 ≤ k → k < n-1 →
      d.q (k : ZMod n) = true → d.q ((k+1 : ℕ) : ZMod n) = true := by
    intro k hk hkn he
    have hk0 : (k : ZMod n) ≠ 0 := by
      intro hh
      have := congrArg ZMod.val hh
      rw [hcast k (by omega)] at this
      simp at this
      omega
    have hk10 : ((k : ZMod n)+1) ≠ 0 := by
      intro hh
      have := congrArg ZMod.val hh
      have hval : ((k : ZMod n)+1).val = k+1 := by
        rw [← Nat.cast_one, ← Nat.cast_add]
        exact hcast _ (by omega)
      rw [hval] at this
      simp at this
    cases hb : d.q ((k+1 : ℕ) : ZMod n) with
    | true => rfl
    | false =>
      have hb' : d.q ((k : ZMod n)+1) = false := by simpa using hb
      obtain h | h := ht.1 (k : ZMod n) he hb'
      · exact False.elim (h (hx _ hk0))
      · exact False.elim (h (hx _ hk10))
  obtain ⟨i, hi, hpat⟩ := bool_prefix (fun k => d.q (k : ZMod n)) (n-1) hpath
  have hin : i < n := by omega
  let j : ZMod n := i
  have hj : j.val = i := hcast i hin
  have hl : chipLevel d = d.x 0 := by
    unfold chipLevel
    exact Finset.sum_eq_single 0 (by intro b _ hb; exact hx b hb) (by simp)
  have heq : d = canonical (chipLevel d) j := by
    have hxx : d.x = (canonical (chipLevel d) j).x := by
      funext k
      by_cases hk : k = 0
      · subst k; simp [canonical, hl]
      · simp [canonical, hk, hx k hk]
    have hqq : d.q = (canonical (chipLevel d) j).q := by
      funext k
      by_cases hk : k = 0
      · subst k; simp [canonical, hq]
      · have hkval : 1 ≤ k.val := by
          have := (ZMod.val_eq_zero k).not.mpr hk
          omega
        have hh := hpat k.val hkval (by have := ZMod.val_lt k; omega)
        simpa [canonical, hj, hkval] using hh
    exact (show ∀ a b : Config n, a.x = b.x → a.q = b.q → a = b from by
      rintro ⟨x,q⟩ ⟨y,r⟩ hx hq; cases hx; cases hq; rfl) _ _ hxx hqq
  have hw : chipWeight d = j := heq ▸ canonical_weight _ j
  simpa [hw] using heq

/-- Unconditional uniqueness normalization. -/
theorem recurrentNormalization : RecurrentNormalization := by
  intro n inst hn c hc
  obtain ⟨d, hd, hdr, hx, hq⟩ := sink_right_exists hn c hc
  have he := sink_classification hn d hdr hx hq
  have hl : chipLevel c = chipLevel d := by
    have := level_reach hd
    rw [level_lift, level_lift] at this
    exact Int.ofNat_inj.mp this
  have hw : chipWeight c = chipWeight d := weight_reach hd
  rw [he, ← hl, ← hw] at hd
  exact hd
end ChanLevine.Sem5
