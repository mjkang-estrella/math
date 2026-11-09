import Sigma.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Sigma365710

theorem F_square_identity (n a : ℕ) :
    16 * F n a = (n : ℤ)^4 - (8 * (a : ℤ) * ((n : ℤ) - a) - (n : ℤ)^2)^2 := by
  unfold F
  ring

theorem exists_bracketing_part {n : ℕ} (hn : 7 ≤ n) :
    ∃ a : ℕ, 1 ≤ a ∧ a < n ∧
      (n : ℤ)^4 - 16 * ((n : ℤ) - 3)^2 ≤ 16 * F n a := by
  have hnz : (7 : ℤ) ≤ n := by exact_mod_cast hn
  let Q : ℕ → Prop := fun t => 8 * (t : ℤ) * ((n : ℤ) - t) ≥ (n : ℤ)^2
  have hex : ∃ t, Q t := by
    refine ⟨n / 2, ?_⟩
    dsimp [Q]
    have he : (n : ℤ) = 2 * ((n : ℤ) / 2) ∨ (n : ℤ) = 2 * ((n : ℤ) / 2) + 1 := by omega
    rcases he with he | he <;> nlinarith [sq_nonneg ((n : ℤ) / 2)]
  let t := Nat.find hex
  have ht : Q t := Nat.find_spec hex
  have hmin : ∀ s < t, ¬ Q s := fun s hs => Nat.find_min hex hs
  have htq : t ≤ n / 2 := by
    apply Nat.find_min' hex
    dsimp [Q]
    have he : (n : ℤ) = 2 * ((n : ℤ) / 2) ∨ (n : ℤ) = 2 * ((n : ℤ) / 2) + 1 := by omega
    rcases he with he | he <;> nlinarith [sq_nonneg ((n : ℤ) / 2)]
  have ht2 : 2 ≤ t := by
    by_contra h
    have hsmall : t = 0 ∨ t = 1 := by omega
    rcases hsmall with h | h <;> rw [h] at ht <;> dsimp [Q] at ht
    · nlinarith
    · have hmul : 0 ≤ ((n : ℤ) - 7) * ((n : ℤ) - 1) := mul_nonneg (by omega) (by omega)
      nlinarith
  have htprev := hmin (t - 1) (by omega)
  have hcast : ((t - 1 : ℕ) : ℤ) = (t : ℤ) - 1 := by omega
  dsimp [Q] at ht htprev
  rw [hcast] at htprev
  push Not at htprev
  have htz : (2 : ℤ) ≤ t := by exact_mod_cast ht2
  have htn : t < n := by omega
  have choose_bound : ∀ a : ℕ, 1 ≤ a → a < n →
      -4 * ((n : ℤ) - 3) ≤ 8 * (a : ℤ) * ((n : ℤ) - a) - (n : ℤ)^2 →
      8 * (a : ℤ) * ((n : ℤ) - a) - (n : ℤ)^2 ≤ 4 * ((n : ℤ) - 3) →
      ∃ a : ℕ, 1 ≤ a ∧ a < n ∧
        (n : ℤ)^4 - 16 * ((n : ℤ) - 3)^2 ≤ 16 * F n a := by
    intro a ha han hl hu
    refine ⟨a,ha,han,?_⟩
    rw [F_square_identity]
    have hm := mul_nonneg (by linarith : 0 ≤ 4 * ((n : ℤ)-3) - (8*(a:ℤ)*((n:ℤ)-a)-(n:ℤ)^2))
      (by linarith : 0 ≤ 4 * ((n : ℤ)-3) + (8*(a:ℤ)*((n:ℤ)-a)-(n:ℤ)^2))
    nlinarith
  by_cases h : 8 * (t : ℤ) * ((n : ℤ)-t) - (n : ℤ)^2 ≤
      - (8 * ((t : ℤ)-1) * ((n : ℤ)-((t : ℤ)-1)) - (n : ℤ)^2)
  · apply choose_bound t (by omega) htn <;> nlinarith
  · apply choose_bound (t-1) (by omega) (by omega) <;> rw [hcast] <;> nlinarith

end Sigma365710
