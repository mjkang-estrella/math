import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic
set_option autoImplicit false
set_option warningAsError true
namespace Diameter48
open SimpleGraph
abbrev V := Fin 12 × Fin 4
def adj (a b : V) : Prop :=
  ((a.1.val + 1) % 12 = b.1.val ∨ (b.1.val + 1) % 12 = a.1.val) ∧ a.2 ≠ b.2
instance : DecidableRel adj := fun a b => inferInstanceAs (Decidable (((a.1.val + 1) % 12 = b.1.val ∨ (b.1.val + 1) % 12 = a.1.val) ∧ a.2 ≠ b.2))
 def G : SimpleGraph V where
  Adj := adj
  symm := ⟨by intro a b h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro a h; exact h.2 rfl⟩
instance : DecidableRel G.Adj := fun a b => inferInstanceAs (Decidable (adj a b))
def cyclic (a b : Fin 12) : ℕ := min ((a.val + 12 - b.val) % 12) ((b.val + 12 - a.val) % 12)
def distance (a b : V) : ℕ :=
  if a = b then 0 else if a.1 = b.1 then 2 else
  if cyclic a.1 b.1 = 1 ∧ a.2 = b.2 then 3 else cyclic a.1 b.1

-- A generic, sound shortest-walk certificate, with no bounded-walk surrogate endpoint.
theorem metric_certificate {W : Type} (H : SimpleGraph W) (d : W → W → ℕ)
    (hz : ∀ a b, d a b = 0 ↔ a = b)
    (hl : ∀ a b c, H.Adj a b → d a c ≤ d b c + 1)
    (hs : ∀ a c, a ≠ c → ∃ b, H.Adj a b ∧ d b c < d a c) :
    ∀ a c, H.dist a c = d a c := by
  have upper : ∀ n a c, d a c = n → ∃ w : H.Walk a c, w.length ≤ n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a c he
      by_cases hac : a = c
      · subst c
        exact ⟨.nil, by simp⟩
      · obtain ⟨b, hab, hbc⟩ := hs a c hac
        obtain ⟨w, hw⟩ := ih (d b c) (by omega) b c rfl
        exact ⟨.cons hab w, by simp only [Walk.length_cons]; omega⟩
  have lower : ∀ {a c} (w : H.Walk a c), d a c ≤ w.length := by
    intro a c w
    induction w with
    | nil => simp [(hz _ _).mpr rfl]
    | @cons a b c hab w ih =>
      have hh := hl a b c hab
      simp only [Walk.length_cons]
      omega
  intro a c
  obtain ⟨w, hw⟩ := upper (d a c) a c rfl
  have hr : H.Reachable a c := ⟨w⟩
  obtain ⟨q, hq⟩ := hr.exists_walk_length_eq_dist
  exact Nat.le_antisymm (le_trans (SimpleGraph.dist_le w) hw) (hq ▸ lower q)

#print axioms metric_certificate
end Diameter48
