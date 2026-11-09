import Mathlib.Data.List.Range
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Nonchalant
abbrev Word := List (Fin 3)
-- Positions are zero based. The suffix length s orders positions from right to left.
def insert (w : Word) (s : Nat) (a : Fin 3) : Word :=
  w.take (w.length - s) ++ [a] ++ w.drop (w.length - s)
def SquareFree (w : Word) : Prop :=
  ∀ i ∈ List.range (w.length + 1), ∀ d ∈ List.range (w.length + 1),
    0 < d → i + 2*d ≤ w.length →
      (w.drop i).take d ≠ (w.drop (i+d)).take d
instance (w : Word) : Decidable (SquareFree w) := inferInstanceAs (Decidable (∀ i ∈ List.range (w.length+1), ∀ d ∈ List.range (w.length+1), 0<d → i+2*d≤w.length → (w.drop i).take d ≠ (w.drop (i+d)).take d))
theorem squareFree_iff (w : Word) : SquareFree w ↔
    ∀ i d : Nat, 0 < d → i+2*d ≤ w.length →
      (w.drop i).take d ≠ (w.drop (i+d)).take d := by
  constructor
  · intro h i d hd hb
    exact h i (List.mem_range.mpr (by omega)) d (List.mem_range.mpr (by omega)) hd hb
  · intro h i _ d _ hd hb
    exact h i d hd hb
-- This is the literal rightmost-position, earliest-letter rule, with no search cutoff.
def Step (w v : Word) : Prop :=
  ∃ s ∈ List.range (w.length+1), ∃ a : Fin 3,
    v = insert w s a ∧ SquareFree v ∧
    ∀ t ∈ List.range (w.length+1), ∀ b : Fin 3,
      (t < s ∨ (t = s ∧ b < a)) → ¬ SquareFree (insert w t b)
instance (w v : Word) : Decidable (Step w v) := inferInstanceAs (Decidable (∃ s ∈ List.range (w.length+1), ∃ a : Fin 3, v=insert w s a ∧ SquareFree v ∧ ∀ t ∈ List.range (w.length+1), ∀ b : Fin 3, (t<s ∨ (t=s ∧ b<a)) → ¬ SquareFree (insert w t b)))
theorem step_unique {w v z : Word} (h : Step w v) (k : Step w z) : v = z := by
  obtain ⟨s, hs, a, hv, hf, hm⟩ := h
  obtain ⟨t, ht, b, hz, hg, hn⟩ := k
  have he : s = t := by
    by_contra hne
    by_cases hlt : s < t
    · exact hn s hs a (Or.inl hlt) (hv ▸ hf)
    · exact hm t ht b (Or.inl (by omega)) (hz ▸ hg)
  subst t
  have hab : a = b := by
    apply Fin.ext
    by_contra hne
    by_cases hlt : a < b
    · exact hn s hs a (Or.inr ⟨rfl,hlt⟩) (hv ▸ hf)
    · exact hm s hs b (Or.inr ⟨rfl,by omega⟩) (hz ▸ hg)
  subst b
  exact hv.trans hz.symm
def internalExtensions (w : Word) : List Word :=
  (((List.range (w.length-1)).flatMap fun s =>
    (List.finRange 3).map fun a => insert w (s+1) a).filter fun v => decide (SquareFree v)).eraseDups
def potential (w : Word) : Nat := (internalExtensions w).length
def InfiniteFrom (w : Word) : Prop :=
  ∃ f : Nat → Word, f 0 = w ∧ ∀ n, Step (f n) (f (n+1))
def SourceConjecture : Prop :=
  ∀ w : Word, SquareFree w → 2 < potential w → InfiniteFrom w
def w0 : Word := [2, 0, 1, 2]
def w1 : Word := [2, 0, 1, 2, 0]
def w2 : Word := [2, 0, 1, 2, 0, 2]
def w3 : Word := [2, 0, 1, 2, 0, 2, 1]
def w4 : Word := [2, 0, 1, 2, 0, 2, 1, 0]
def w5 : Word := [2, 0, 1, 2, 0, 2, 1, 0, 1]
def w6 : Word := [2, 0, 1, 2, 0, 2, 1, 0, 1, 2]
def w7 : Word := [2, 0, 1, 2, 0, 2, 1, 0, 1, 2, 0]
def w8 : Word := [2, 0, 1, 2, 0, 2, 1, 0, 1, 2, 0, 1]
def w9 : Word := [2, 0, 1, 2, 0, 2, 1, 0, 1, 2, 0, 1, 0]
def w10 : Word := [2, 0, 1, 2, 0, 2, 1, 0, 1, 2, 0, 1, 0, 2]
def w11 : Word := [2, 0, 1, 2, 0, 2, 1, 0, 1, 2, 0, 1, 0, 2, 0]
def w12 : Word := [2, 0, 1, 2, 0, 2, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1]
def w13 : Word := [2, 0, 1, 2, 0, 2, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1, 2]
def w14 : Word := [2, 0, 1, 2, 0, 2, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0]
def w15 : Word := [2, 0, 1, 2, 0, 2, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 2]
def w16 : Word := [2, 0, 1, 2, 0, 2, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 2, 1]
def w17 : Word := [2, 0, 1, 2, 0, 2, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 2, 1, 0]
def w18 : Word := [2, 0, 1, 2, 0, 2, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 2, 1, 0, 1]
def w19 : Word := [2, 0, 1, 2, 0, 2, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 2, 1, 0, 1, 2]
def w20 : Word := [2, 0, 1, 2, 0, 2, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 2, 1, 0, 1, 2, 0]
def w21 : Word := [2, 0, 1, 2, 0, 2, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 2, 1, 0, 1, 2, 0, 1]
theorem seed_squarefree : SquareFree w0 := by decide
theorem seed_potential : potential w0 = 3 := by decide
theorem move0 : Step w0 w1 := by decide
theorem move1 : Step w1 w2 := by decide
theorem move2 : Step w2 w3 := by decide
theorem move3 : Step w3 w4 := by decide
theorem move4 : Step w4 w5 := by decide
theorem move5 : Step w5 w6 := by decide
theorem move6 : Step w6 w7 := by decide
theorem move7 : Step w7 w8 := by decide
theorem move8 : Step w8 w9 := by decide
theorem move9 : Step w9 w10 := by decide
theorem move10 : Step w10 w11 := by decide
theorem move11 : Step w11 w12 := by decide
theorem move12 : Step w12 w13 := by decide
theorem move13 : Step w13 w14 := by decide
theorem move14 : Step w14 w15 := by decide
theorem move15 : Step w15 w16 := by decide
theorem move16 : Step w16 w17 := by decide
theorem move17 : Step w17 w18 := by decide
theorem move18 : Step w18 w19 := by decide
theorem move19 : Step w19 w20 := by decide
theorem move20 : Step w20 w21 := by decide
theorem terminal : ∀ s ∈ List.range (w21.length+1), ∀ a : Fin 3,
    ¬ SquareFree (insert w21 s a) := by decide
theorem no_terminal_step (v : Word) : ¬ Step w21 v := by
  rintro ⟨s,hs,a,hv,hf,_⟩
  exact terminal s hs a (hv ▸ hf)
theorem finite_trajectory : ¬ InfiniteFrom w0 := by
  rintro ⟨f,h0,h⟩
  have e1 : f 1 = w1 := by
    have hh := h 0
    rw [h0] at hh
    exact step_unique hh move0
  have e2 : f 2 = w2 := by
    have hh := h 1
    rw [e1] at hh
    exact step_unique hh move1
  have e3 : f 3 = w3 := by
    have hh := h 2
    rw [e2] at hh
    exact step_unique hh move2
  have e4 : f 4 = w4 := by
    have hh := h 3
    rw [e3] at hh
    exact step_unique hh move3
  have e5 : f 5 = w5 := by
    have hh := h 4
    rw [e4] at hh
    exact step_unique hh move4
  have e6 : f 6 = w6 := by
    have hh := h 5
    rw [e5] at hh
    exact step_unique hh move5
  have e7 : f 7 = w7 := by
    have hh := h 6
    rw [e6] at hh
    exact step_unique hh move6
  have e8 : f 8 = w8 := by
    have hh := h 7
    rw [e7] at hh
    exact step_unique hh move7
  have e9 : f 9 = w9 := by
    have hh := h 8
    rw [e8] at hh
    exact step_unique hh move8
  have e10 : f 10 = w10 := by
    have hh := h 9
    rw [e9] at hh
    exact step_unique hh move9
  have e11 : f 11 = w11 := by
    have hh := h 10
    rw [e10] at hh
    exact step_unique hh move10
  have e12 : f 12 = w12 := by
    have hh := h 11
    rw [e11] at hh
    exact step_unique hh move11
  have e13 : f 13 = w13 := by
    have hh := h 12
    rw [e12] at hh
    exact step_unique hh move12
  have e14 : f 14 = w14 := by
    have hh := h 13
    rw [e13] at hh
    exact step_unique hh move13
  have e15 : f 15 = w15 := by
    have hh := h 14
    rw [e14] at hh
    exact step_unique hh move14
  have e16 : f 16 = w16 := by
    have hh := h 15
    rw [e15] at hh
    exact step_unique hh move15
  have e17 : f 17 = w17 := by
    have hh := h 16
    rw [e16] at hh
    exact step_unique hh move16
  have e18 : f 18 = w18 := by
    have hh := h 17
    rw [e17] at hh
    exact step_unique hh move17
  have e19 : f 19 = w19 := by
    have hh := h 18
    rw [e18] at hh
    exact step_unique hh move18
  have e20 : f 20 = w20 := by
    have hh := h 19
    rw [e19] at hh
    exact step_unique hh move19
  have e21 : f 21 = w21 := by
    have hh := h 20
    rw [e20] at hh
    exact step_unique hh move20
  have hh := h 21
  rw [e21] at hh
  exact no_terminal_step (f 22) hh
theorem source_refutation : ¬ SourceConjecture := by
  intro h
  exact finite_trajectory (h w0 seed_squarefree (by rw [seed_potential]; decide))
#print axioms source_refutation
end Nonchalant
