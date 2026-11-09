import Game
set_option autoImplicit false
namespace Review
open MathDB355140
theorem number_le_iff {n : ℕ} (G : SimpleGraph (Fin n)) (turn : Bool) (B : ℕ) :
    winningNumber G turn ≤ (B : WithTop ℕ) ↔ Wins G ∅ Finset.univ turn B := by
  classical
  unfold winningNumber
  split_ifs with h
  · constructor
    · intro hle
      have hn : Nat.find h ≤ B := by exact_mod_cast hle
      exact (Nat.find_spec h).mono B hn
    · intro hw
      have hn := Nat.find_min' h hw
      exact_mod_cast hn
  · constructor
    · intro hle
      have ht : (B : WithTop ℕ) = ⊤ := top_le_iff.mp hle
      simp at ht
    · intro hw
      exact False.elim (h ⟨B,hw⟩)
example : check (⊥ : SimpleGraph (Fin 0)) ∅ ∅ false 5 = false := by decide +kernel
example : check (⊥ : SimpleGraph (Fin 1)) ∅ ∅ false 5 = false := by decide +kernel
example : check (⊥ : SimpleGraph (Fin 1)) ∅ Finset.univ true 1 = true := by decide +kernel
example : check (⊥ : SimpleGraph (Fin 1)) ∅ Finset.univ false 1 = false := by decide +kernel
example : (7+1)/2-2+1 = (3 : ℕ) := by decide
#print axioms number_le_iff
end Review
