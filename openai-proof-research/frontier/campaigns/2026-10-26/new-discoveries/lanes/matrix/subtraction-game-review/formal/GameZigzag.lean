import GameRecurrence

open Finset
namespace OddSubtraction

lemma eligible_mem {S : Finset ℕ} {n k : ℕ} :
    k ∈ eligible S n ↔ k ∈ S ∧ k≤n := by simp [eligible]

lemma eligible_mono (S : Finset ℕ) {n m : ℕ} (h : n ≤ m) :
    eligible S n ⊆ eligible S m := by
  intro k hk
  rcases eligible_mem.mp hk with ⟨hk, hn⟩
  exact eligible_mem.mpr ⟨hk, hn.trans h⟩

lemma eligible_odd_succ {S : Finset ℕ} (hodd : ∀ k ∈ S,k % 2=1) {n : ℕ}
    (hn : n % 2=1) : eligible S (n+1)=eligible S n := by
  ext k
  simp only [eligible_mem]
  constructor
  · rintro ⟨hk, hkn⟩
    exact ⟨hk, by have h := hodd k hk; omega⟩
  · rintro ⟨hk, hkn⟩
    exact ⟨hk, by omega⟩

lemma consecutive_zigzag {S : Finset ℕ} {a : ℕ → ℝ}
    (hm : Model S a) (hodd : ∀ k ∈ S,k % 2=1) :
    ∀ n, if n % 2=0 then a n≤a (n+1) else a (n+1)≤a n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n % 2=0
    · simp only [hn, ite_true]
      by_cases he : eligible S n=∅
      · rw [hm.empty n he]
        exact hm.nonneg _
      · have hne : (eligible S n).Nonempty := Finset.nonempty_iff_ne_empty.mpr he
        have hpos : (0:ℝ)<(eligible S (n+1)).card := by
          exact_mod_cast Finset.card_pos.mpr (hne.mono (eligible_mono S (Nat.le_succ n)))
        have hsum : (∑k ∈ eligible S (n+1),a (n + 1 - k)) ≤
            ∑k ∈ eligible S n,a (n - k) := by
          have heq : (∑k ∈ eligible S (n+1),a (n + 1 - k)) =
              ∑k ∈ eligible S n,a (n + 1 - k) := by
            symm
            apply Finset.sum_subset (eligible_mono S (Nat.le_succ n))
            intro k hk hkn
            have hk' := eligible_mem.mp hk
            have hnk : k=n+1 := by
              have : ¬ k ≤ n := by intro h; exact hkn (eligible_mem.mpr ⟨hk'.1,h⟩)
              omega
            subst k
            have hezero : eligible S 0=∅ := by
              apply Finset.eq_empty_iff_forall_notMem.mpr
              intro k hk
              have hk' := eligible_mem.mp hk
              have hko := hodd k hk'.1
              omega
            simpa using hm.empty 0 hezero
          rw [heq]
          apply Finset.sum_le_sum
          intro k hk
          have hk' := eligible_mem.mp hk
          have hko := hodd k hk'.1
          have hlt : n - k<n := by omega
          have hpar : (n - k) % 2≠0 := by omega
          have hsub : n + 1 - k=(n - k)+1 := by omega
          simpa only [hpar, ite_false, hsub] using ih (n - k) hlt
        have hcard : ((eligible S n).card:ℝ)≤(eligible S (n+1)).card := by
          exact_mod_cast Finset.card_le_card (eligible_mono S (Nat.le_succ n))
        have hbal := hm.balance n
        have hbal' := hm.balance (n+1)
        have hn1 := hm.le_one n
        nlinarith
    · simp only [hn, ite_false]
      have hnodd : n % 2=1 := by omega
      have heq := eligible_odd_succ hodd hnodd
      by_cases he : eligible S n=∅
      · rw [hm.empty n he, hm.empty (n+1) (heq.trans he)]
      · have hpos : (0:ℝ)<(eligible S n).card := by
          exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
        have hsum : (∑k ∈ eligible S n,a (n - k))≤∑k ∈ eligible S n,a (n + 1 - k) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk' := eligible_mem.mp hk
          have hko := hodd k hk'.1
          have hlt : n - k<n := by omega
          have hpar : (n - k) % 2=0 := by omega
          have hsub : n + 1 - k=(n - k)+1 := by omega
          simpa only [hpar, ite_true, hsub] using ih (n - k) hlt
        have hbal := hm.balance n
        have hbal' := hm.balance (n+1)
        rw [heq] at hbal'
        nlinarith

lemma zigzag_even {S : Finset ℕ} {a : ℕ → ℝ}
    (hm : Model S a) (hodd : ∀ k ∈ S,k % 2=1) (m : ℕ) :
    a (2*m)≤a (2*m+1) := by
  simpa using consecutive_zigzag hm hodd (2*m)

lemma zigzag_odd {S : Finset ℕ} {a : ℕ → ℝ}
    (hm : Model S a) (hodd : ∀ k ∈ S,k % 2=1) (m : ℕ) :
    a (2*m+2)≤a (2*m+1) := by
  simpa [Nat.add_assoc] using consecutive_zigzag hm hodd (2*m+1)

lemma model_zero {S : Finset ℕ} {a : ℕ → ℝ}
    (hm : Model S a) (hodd : ∀ k ∈ S,k % 2=1) : a 0=0 := by
  apply hm.empty
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  have hk' := eligible_mem.mp hk
  have hko := hodd k hk'.1
  omega

lemma prefixSum_succ (c : ℕ → ℝ) (n : ℕ) :
    prefixSum c (n+1)=prefixSum c n+c n := by
  simp [prefixSum, Finset.sum_range_succ]

lemma odd_prefix_step (a : ℕ → ℝ) (m : ℕ) :
    prefixSum (centered a) (2*(m+1)+1) =
      prefixSum (centered a) (2*m+1)+2*(a (2*m+1)-a (2*m+2)) := by
  rw [show 2*(m+1)+1=(2*m+1)+1+1 by omega, prefixSum_succ, prefixSum_succ]
  simp [centered, pow_add, pow_mul]
  ring

lemma odd_prefix_positive {S : Finset ℕ} {a : ℕ → ℝ}
    (hm : Model S a) (hodd : ∀ k ∈ S,k % 2=1) (k : ℕ) (hk : k % 2=1) :
    1≤prefixSum (centered a) k := by
  have h : ∀ m, 1≤prefixSum (centered a) (2*m+1) := by
    intro m
    induction m with
    | zero => simp [prefixSum, centered, model_zero hm hodd]
    | succ m ih =>
      rw [odd_prefix_step]
      have hz := zigzag_odd hm hodd m
      linarith
  have hk' : k=2*(k/2)+1 := by omega
  rw [hk']
  exact h (k/2)

end OddSubtraction
