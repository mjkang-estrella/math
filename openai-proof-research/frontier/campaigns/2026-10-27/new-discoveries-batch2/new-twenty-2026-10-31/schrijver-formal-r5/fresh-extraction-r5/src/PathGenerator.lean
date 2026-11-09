import Enumeration
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

noncomputable def pathMasks : ℕ → ℕ → List ℕ
  | _, 0 => [0]
  | 0, _ + 1 => []
  | n + 1, k + 1 => pathMasks n (k + 1) ++ ((match n with | 0 => pathMasks 0 k | t + 1 => pathMasks t k)).map (fun m => 2^n ||| m)
termination_by structural n _ => n

theorem pathMasks_step (n k : ℕ) :
    pathMasks (n+1) (k+1) = pathMasks n (k+1) ++ (pathMasks (n-1) k).map (fun m => 2^n ||| m) := by
  cases n <;> rfl

theorem pathMasks_cover (n : ℕ) (s : Finset ℕ)
    (hb : ∀ a ∈ s, a < n) (hs : ∀ a ∈ s, a + 1 ∉ s) :
    encodeList s.toList ∈ pathMasks n s.card := by
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
    by_cases he : s = ∅
    · subst s; simp [encodeList, pathMasks]
    have hc : s.card ≠ 0 := by simpa using he
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hc
    cases n with
    | zero =>
      have : s = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by intro a ha; have := hb a ha; omega)
      exact (he this).elim
    | succ n =>
      rw [hk, pathMasks_step]
      by_cases hn : n ∈ s
      · apply List.mem_append_right
        apply List.mem_map.mpr
        refine ⟨encodeList (s.erase n).toList, ?_, ?_⟩
        · have hb' : ∀ a ∈ s.erase n, a < n - 1 := by
            intro a ha
            obtain ⟨han, has⟩ := Finset.mem_erase.mp ha
            have hlt := hb a has
            have hne := hs a has
            by_cases hn0 : n = 0
            · omega
            · by_contra hh
              have : a + 1 = n := by omega
              exact hne (this ▸ hn)
          have hcard : (s.erase n).card = k := by
            have := Finset.card_erase_add_one hn
            omega
          rw [← hcard]
          exact ih (n - 1) (by omega) _ hb' (by
            intro a ha hh
            exact hs a (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hh))
        · apply Nat.eq_of_testBit_eq
          intro i
          simp only [Nat.testBit_or, Nat.testBit_two_pow, encodeList_bit,
            Finset.mem_toList, Finset.mem_erase]
          by_cases hi : i = n
          · subst i; simp [hn]
          · simp [hi, Ne.symm hi]
      · apply List.mem_append_left
        change encodeList s.toList ∈ pathMasks n k.succ
        rw [← hk]
        exact ih n (by omega) s (by
          intro a ha
          have := hb a ha
          have : a ≠ n := by intro h; exact hn (h ▸ ha)
          omega) hs
end Schrijver
