import GameZigzag

open Finset
namespace OddSubtraction

/-- Uniformly randomized legal positive subtraction, losing if no legal move exists. -/
noncomputable def gameWin (S : Finset ℕ) (n : ℕ) : ℝ :=
  if eligible S n = ∅ then 0 else
    1 - (∑ k∈S, if _hk : 0<k ∧ k≤n then gameWin S (n-k) else 0) /
      ((eligible S n).card:ℝ)
termination_by n
decreasing_by omega

lemma gameWin_recurrence (S : Finset ℕ) (hpos : ∀ k∈S, 0<k) (n : ℕ) :
    gameWin S n = if eligible S n=∅ then 0 else
      1 - (∑ k∈eligible S n, gameWin S (n-k)) / ((eligible S n).card:ℝ) := by
  rw [gameWin]
  split_ifs with he
  · rfl
  · congr 2
    rw [eligible, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hkn : k≤n
    · simp [hkn, hpos k hk]
    · simp [hkn]

lemma gameWin_bounds (S : Finset ℕ) (hpos : ∀ k∈S, 0<k) :
    ∀ n, 0≤gameWin S n ∧ gameWin S n≤1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [gameWin_recurrence S hpos]
    split_ifs with he
    · norm_num
    · have hcard : (0:ℝ)<(eligible S n).card := by
        exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
      have hnonneg : (0:ℝ)≤∑ k∈eligible S n, gameWin S (n-k) := by
        apply Finset.sum_nonneg
        intro k hk
        have hk' := eligible_mem.mp hk
        exact (ih (n-k) (by have hp := hpos k hk'.1; omega)).1
      have hupper : (∑ k∈eligible S n, gameWin S (n-k)) ≤ (eligible S n).card := by
        calc
          _ ≤ ∑ k∈eligible S n, (1:ℝ) := by
            apply Finset.sum_le_sum
            intro k hk
            have hk' := eligible_mem.mp hk
            exact (ih (n-k) (by have hp := hpos k hk'.1; omega)).2
          _ = _ := by simp
      constructor
      · have hdiv := (div_le_one hcard).mpr hupper
        linarith
      · have hdiv := div_nonneg hnonneg (le_of_lt hcard)
        linarith

theorem gameWin_model (S : Finset ℕ) (hpos : ∀ k∈S, 0<k) : Model S (gameWin S) := by
  constructor
  · intro n
    exact (gameWin_bounds S hpos n).1
  · intro n
    exact (gameWin_bounds S hpos n).2
  · intro n he
    simp [gameWin_recurrence S hpos n, he]
  · intro n
    rw [gameWin_recurrence S hpos]
    split_ifs with he
    · simp [he]
    · have hcard : ((eligible S n).card:ℝ)≠0 := by
        exact_mod_cast Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr he)
      field_simp

lemma model_unique {S : Finset ℕ} {a b : ℕ → ℝ}
    (ha : Model S a) (hb : Model S b) (hpos : ∀ k∈S, 0<k) : a=b := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases he : eligible S n=∅
    · rw [ha.empty n he, hb.empty n he]
    · have hcard : ((eligible S n).card:ℝ)≠0 := by
        exact_mod_cast Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr he)
      have hsum : (∑ k∈eligible S n,a (n-k)) = ∑ k∈eligible S n,b (n-k) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' := eligible_mem.mp hk
        exact ih (n-k) (by have hp := hpos k hk'.1; omega)
      have hba := ha.balance n
      have hbb := hb.balance n
      rw [hsum] at hba
      exact (mul_left_cancel₀ hcard) (hba.trans hbb.symm)

lemma gameWin_uniform (S : Finset ℕ) (hpos : ∀ k∈S, 0<k) (n : ℕ)
    (hne : (eligible S n).Nonempty) :
    gameWin S n = 1 - (∑ k∈eligible S n, gameWin S (n-k)) /
      ((eligible S n).card:ℝ) := by
  rw [gameWin_recurrence S hpos]
  simp only [Finset.nonempty_iff_ne_empty.mp hne, ite_false]

end OddSubtraction
