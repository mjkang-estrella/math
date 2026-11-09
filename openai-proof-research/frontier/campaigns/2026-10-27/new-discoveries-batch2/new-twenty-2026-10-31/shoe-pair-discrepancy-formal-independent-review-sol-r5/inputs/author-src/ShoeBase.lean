import Mathlib.Probability.ProbabilityMassFunction.Basic
import Lean.Elab.Tactic.Omega

/-! Source: Arratia--DeSalvo, final Sections 2, 4, 9.1--9.2.
Time indices here are zero based: 0 is L₁, 1 is R₁, 2 is L₂.
A prefix of length n contains exactly positions strictly below n.
These definitions do not assume termination or a winning-color estimate. -/
namespace Shoe

attribute [local instance] Classical.propDecidable

abbrev DiscreteLaw (α : Type*) := PMF α
abbrev Sample (α : Type*) := ℕ → α

def HasMatch {α : Type*} (ω : Sample α) (n : ℕ) : Prop :=
  ∃ a b : ℕ, 2 * a < n ∧ 2 * b + 1 < n ∧ ω (2 * a) = ω (2 * b + 1)

def FirstMatch {α : Type*} (ω : Sample α) (n : ℕ) : Prop :=
  HasMatch ω (n + 1) ∧ ¬ HasMatch ω n

def Terminates {α : Type*} (ω : Sample α) : Prop := ∃ n, HasMatch ω n

noncomputable def firstLength {α : Type*} (ω : Sample α)
    (h : Terminates ω) : ℕ := Nat.find h

noncomputable def winner {α : Type*} [Inhabited α] (ω : Sample α) : α :=
  if h : Terminates ω then ω (firstLength ω h - 1) else default

theorem hasMatch_mono {α : Type*} {ω : Sample α} {m n : ℕ}
    (hmn : m ≤ n) (h : HasMatch ω m) : HasMatch ω n := by
  obtain ⟨a, b, ha, hb, he⟩ := h
  exact ⟨a, b, lt_of_lt_of_le ha hmn, lt_of_lt_of_le hb hmn, he⟩

theorem no_match_empty {α : Type*} (ω : Sample α) : ¬ HasMatch ω 0 := by
  rintro ⟨a, b, ha, hb, he⟩
  omega

theorem firstLength_spec {α : Type*} (ω : Sample α) (h : Terminates ω) :
    HasMatch ω (firstLength ω h) := Nat.find_spec h

theorem firstLength_min {α : Type*} (ω : Sample α) (h : Terminates ω)
    {n : ℕ} (hn : n < firstLength ω h) : ¬ HasMatch ω n :=
  Nat.find_min h hn

/-- At a first intersection, every matching pair has the new shoe's color.
This includes both left and right arrivals; no simultaneous-pair tie rule occurs. -/
theorem firstMatch_color {α : Type*} {ω : Sample α} {n a b : ℕ}
    (h : FirstMatch ω n) (ha : 2 * a < n + 1) (hb : 2 * b + 1 < n + 1)
    (he : ω (2 * a) = ω (2 * b + 1)) : ω (2 * a) = ω n := by
  by_cases hl : 2 * a < n
  · have hr : 2 * b + 1 = n := by
      by_contra hn
      have : 2 * b + 1 < n := by omega
      exact h.2 ⟨a, b, hl, this, he⟩
    simpa only [hr] using he
  · have : 2 * a = n := by omega
    rw [this]

/-- Failure through 2N shoes implies all N aligned pairs are unequal. -/
theorem no_match_diagonal {α : Type*} {ω : Sample α} {N : ℕ}
    (h : ¬ HasMatch ω (2 * N)) {j : ℕ} (hj : j < N) :
    ω (2 * j) ≠ ω (2 * j + 1) := by
  intro he
  apply h
  exact ⟨j, j, by omega, by omega, he⟩

end Shoe
