import ShoeStopping

namespace Shoe

/-- Only i is common to the two initial K-blocks. Same-side repetitions are allowed. -/
def OnlyCommon {α : Type*} (ω : Sample α) (K : ℕ) (i : α) : Prop :=
  ∀ a < K, ∀ b < K, ω (2*a) = ω (2*b+1) → ω (2*a) = i

/-- E_ab: exactly the indicated positions on each side have color i. -/
def Isolated {α : Type*} (ω : Sample α) (K a b : ℕ) (i : α) : Prop :=
  a < K ∧ b < K ∧ ω (2*a) = i ∧ ω (2*b+1) = i ∧
  (∀ c < K, c ≠ a → ω (2*c) ≠ i) ∧
  (∀ d < K, d ≠ b → ω (2*d+1) ≠ i)

/-- F_ab: the isolated occurrences survive every other cross-side collision. -/
def GoodBlock {α : Type*} (ω : Sample α) (K a b : ℕ) (i : α) : Prop :=
  Isolated ω K a b i ∧
  ∀ c < K, ∀ d < K, c ≠ a → d ≠ b → ω (2*c) ≠ ω (2*d+1)

theorem goodBlock_onlyCommon {α : Type*} {ω : Sample α} {K a b : ℕ} {i : α}
    (h : GoodBlock ω K a b i) : OnlyCommon ω K i := by
  intro c hc d hd he
  by_cases hca : c = a
  · simpa only [hca] using h.1.2.2.1
  · by_cases hdb : d = b
    · rw [he, hdb]
      exact h.1.2.2.2.1
    · exact False.elim (h.2 c hc d hd hca hdb he)

/-- A match within the initial block and no other common color force the actual
least chronological winner. Coordinates after the block are unrestricted. -/
theorem winner_of_onlyCommon {α : Type*} [Inhabited α] {ω : Sample α}
    {K a b : ℕ} {i : α} (ha : a < K) (hb : b < K)
    (he : ω (2*a) = ω (2*b+1)) (ho : OnlyCommon ω K i) : winner ω = i := by
  classical
  have hm : HasMatch ω (2*K) := ⟨a,b,by omega,by omega,he⟩
  have ht : Terminates ω := ⟨2*K,hm⟩
  have hl : firstLength ω ht ≤ 2*K := Nat.find_le hm
  have hf := first_at_least ω ht
  obtain ⟨c,d,hc,hd,hcd⟩ := hf.1
  have hcK : c < K := by omega
  have hdK : d < K := by omega
  have hw := firstMatch_color hf hc hd hcd
  exact (winner_at_first hf).trans (hw.symm.trans (ho c hcK d hdK hcd))

theorem winner_of_goodBlock {α : Type*} [Inhabited α] {ω : Sample α}
    {K a b : ℕ} {i : α} (h : GoodBlock ω K a b i) : winner ω = i := by
  apply winner_of_onlyCommon h.1.1 h.1.2.1
  · exact h.1.2.2.1.trans h.1.2.2.2.1.symm
  · exact goodBlock_onlyCommon h

theorem isolated_positions_unique {α : Type*} {ω : Sample α}
    {K a b c d : ℕ} {i : α} (h : Isolated ω K a b i)
    (h' : Isolated ω K c d i) : a = c ∧ b = d := by
  constructor
  · by_contra hn
    exact h.2.2.2.2.1 c h'.1 (Ne.symm hn) h'.2.2.1
  · by_contra hn
    exact h.2.2.2.2.2 d h'.2.1 (Ne.symm hn) h'.2.2.2.1

/-- The first pair branch uses strict alternation literally. -/
theorem winner_first_pair {α : Type*} [Inhabited α] {ω : Sample α}
    (h : ω 0 = ω 1) : winner ω = ω 0 := by
  have hf : FirstMatch ω 1 := by
    constructor
    · exact ⟨0,0,by omega,by omega,h⟩
    · rintro ⟨a,b,ha,hb,he⟩
      omega
  exact (winner_at_first hf).trans h.symm

end Shoe
