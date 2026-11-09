import CycDefs

/-!
# Rotation lemma

If `q : Fin k → ℕ` is strictly increasing and all values lie in a window `[q 0, q 0 + N)`, then
`i ↦ q i mod N` is a cyclic embedding into `Fin N`.
-/

namespace CycRamsey

theorem mod_of_bounds {x c N : ℕ} (h1 : c * N ≤ x) (h2 : x < (c + 1) * N) : x % N = x - c * N := by
  have hd : x / N = c := Nat.div_eq_of_lt_le h1 h2
  rw [Nat.mod_eq_sub_mul_div, hd, Nat.mul_comm]

theorem rot_embedding {k N : ℕ} (hN : 0 < N) (hk : 0 < k) (q : Fin k → ℕ) (hq : StrictMono q)
    (hspan : ∀ i : Fin k, q i < q ⟨0, hk⟩ + N) :
    IsCyclicEmbedding (fun i => (⟨q i % N, Nat.mod_lt _ hN⟩ : Fin N)) := by
  set q0 := q ⟨0, hk⟩ with hq0
  set c0 := q0 / N with hc0
  have hq0lo : c0 * N ≤ q0 := by
    have := Nat.div_mul_le_self q0 N
    simpa [hc0] using this
  have hq0hi : q0 < (c0 + 1) * N := by
    have := Nat.lt_div_mul_add (a := q0) hN
    rw [Nat.add_mul, one_mul]; simpa [hc0] using this
  have hge0 : ∀ i : Fin k, q0 ≤ q i := by
    intro i
    rcases Nat.eq_zero_or_pos i.val with h | h
    · have : i = ⟨0, hk⟩ := Fin.ext h
      rw [this]
    · exact le_of_lt (hq (show (⟨0, hk⟩ : Fin k) < i from h))
  -- first index whose value reaches the next multiple of `N`
  have hex : ∃ i : ℕ, k ≤ i ∨ ∃ h : i < k, (c0 + 1) * N ≤ q ⟨i, h⟩ := ⟨k, Or.inl le_rfl⟩
  classical
  set T := Nat.find hex with hT
  have hTk : T ≤ k := Nat.find_min' hex (Or.inl le_rfl)
  have hlo : ∀ (i : ℕ) (h : i < k), i < T → q ⟨i, h⟩ % N = q ⟨i, h⟩ - c0 * N := by
    intro i h hiT
    have hn := Nat.find_min hex hiT
    push Not at hn
    have h2 : q ⟨i, h⟩ < (c0 + 1) * N := hn.2 h
    exact mod_of_bounds (le_trans hq0lo (hge0 _)) h2
  have hhige : ∀ (i : ℕ) (h : i < k), T ≤ i → (c0 + 1) * N ≤ q ⟨i, h⟩ := by
    intro i h hTi
    have hTlt : T < k := lt_of_le_of_lt hTi h
    have hs := Nat.find_spec hex
    rcases hs with hs | ⟨hTk', hs⟩
    · exact absurd hs (by omega)
    refine le_trans hs ?_
    rcases Nat.lt_or_ge T i with h' | h'
    · exact le_of_lt (hq (show (⟨T, hTk'⟩ : Fin k) < ⟨i, h⟩ from h'))
    · have : T = i := le_antisymm hTi h'
      subst this; exact le_rfl
  have hhi : ∀ (i : ℕ) (h : i < k), T ≤ i → q ⟨i, h⟩ % N = q ⟨i, h⟩ - (c0 + 1) * N := by
    intro i h hTi
    have hTlt : T < k := lt_of_le_of_lt hTi h
    have hs := Nat.find_spec hex
    rcases hs with hs | ⟨hTk', hs⟩
    · exact absurd hs (by omega)
    have h1 : (c0 + 1) * N ≤ q ⟨i, h⟩ := by
      refine le_trans hs ?_
      rcases Nat.lt_or_ge T i with h' | h'
      · exact le_of_lt (hq (show (⟨T, hTk'⟩ : Fin k) < ⟨i, h⟩ from h'))
      · have : T = i := le_antisymm hTi h'
        subst this; exact le_rfl
    have h2 : q ⟨i, h⟩ < (c0 + 1 + 1) * N := by
      have := hspan ⟨i, h⟩
      have : (c0 + 1 + 1) * N = (c0 + 1) * N + N := by ring
      omega
    exact mod_of_bounds h1 h2
  -- index arithmetic for the rotation start `t = T mod k`
  set t : Fin k := ⟨T % k, Nat.mod_lt _ hk⟩ with ht
  have hidx : ∀ j : Fin k, (t + j).val = if T + j.val < k then T + j.val else T + j.val - k := by
    intro j
    rw [Fin.val_add]
    simp only [ht]
    rw [Nat.mod_add_mod]
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  have hmono : ∀ (i1 i2 : ℕ) (h1 : i1 < k) (h2 : i2 < k), i1 < i2 → q ⟨i1, h1⟩ < q ⟨i2, h2⟩ :=
    fun i1 i2 h1 h2 h => hq (show (⟨i1, h1⟩ : Fin k) < ⟨i2, h2⟩ from h)
  have hsm : StrictMono (fun j : Fin k => (⟨q (t + j) % N, Nat.mod_lt _ hN⟩ : Fin N)) := by
    intro j1 j2 hj
    have hj' : j1.val < j2.val := hj
    show q (t + j1) % N < q (t + j2) % N
    have e1 := hidx j1
    have e2 := hidx j2
    have hb1 : (t + j1).val < k := (t + j1).isLt
    have hb2 : (t + j2).val < k := (t + j2).isLt
    have r1 : q (t + j1) = q ⟨(t + j1).val, hb1⟩ := rfl
    have r2 : q (t + j2) = q ⟨(t + j2).val, hb2⟩ := rfl
    rw [r1, r2]
    by_cases c2 : T + j2.val < k
    · -- both indices are `≥ T`
      have c1 : T + j1.val < k := by omega
      simp only [c1, c2, ite_true] at e1 e2
      rw [hhi _ hb1 (by omega), hhi _ hb2 (by omega)]
      have := hmono _ _ hb1 hb2 (by omega)
      have := hhige _ hb1 (by omega)
      omega
    · simp only [c2, ite_false] at e2
      by_cases c1 : T + j1.val < k
      · simp only [c1, ite_true] at e1
        rw [hhi _ hb1 (by omega), hlo _ hb2 (by omega)]
        have a1 := hspan ⟨(t + j1).val, hb1⟩
        have a2 := hge0 ⟨(t + j2).val, hb2⟩
        have a3 := hhige _ hb1 (by omega)
        have : (c0 + 1) * N = c0 * N + N := by ring
        omega
      · simp only [c1, ite_false] at e1
        rw [hlo _ hb1 (by omega), hlo _ hb2 (by omega)]
        have := hmono _ _ hb1 hb2 (by omega)
        have := hge0 ⟨(t + j1).val, hb1⟩
        omega
  refine ⟨?_, t, hsm⟩
  -- injectivity from the rotated strict monotonicity
  intro x y hxy
  have hsurj : ∀ x : Fin k, ∃ j : Fin k, t + j = x := by
    intro x
    refine ⟨⟨(x.val + k - t.val) % k, Nat.mod_lt _ hk⟩, ?_⟩
    apply Fin.ext
    rw [Fin.val_add]
    simp only
    rw [Nat.add_mod_mod]
    have : t.val + (x.val + k - t.val) = x.val + k := by have := t.isLt; omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt]
  obtain ⟨jx, rfl⟩ := hsurj x
  obtain ⟨jy, rfl⟩ := hsurj y
  have := hsm.injective (a₁ := jx) (a₂ := jy) hxy
  rw [this]

end CycRamsey
