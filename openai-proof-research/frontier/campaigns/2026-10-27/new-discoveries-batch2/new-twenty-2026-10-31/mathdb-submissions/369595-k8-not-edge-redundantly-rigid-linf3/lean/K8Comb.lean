import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Tactic.Linarith

/-!
# The combinatorial shadow of an edge-redundantly rigid placement of `K₈` in `ℓ∞³`

`Dom x k`: coordinate `k` is the unique coordinate of largest absolute value of
`x`.  `Good p` collects the two consequences of edge-redundant rigidity that the
refutation uses (proved in `LinfBridge`):
* every pair of distinct points has a dominant coordinate;
* for every edge `uv`, every cut `(S, V ∖ S)` and every colour `k`, some edge
  other than `uv` crossing the cut has colour `k`.

`Anchored p` is the symmetry-normalised form used by the propositional instance.
-/

namespace K8

/-- Coordinate `k` strictly dominates every other coordinate in absolute value. -/
def Dom {d : ℕ} (x : Fin d → ℝ) (k : Fin d) : Prop := ∀ j, j ≠ k → |x j| < |x k|

structure Good (p : Fin 8 → Fin 3 → ℝ) : Prop where
  dom : ∀ u v : Fin 8, u ≠ v → ∃ k, Dom (p v - p u) k
  cut : ∀ u v : Fin 8, u ≠ v → ∀ (S : Finset (Fin 8)) (k : Fin 3), (∃ a, a ∈ S) → (∃ b, b ∉ S) →
    ∃ a ∈ S, ∃ b, b ∉ S ∧ ¬ (a = u ∧ b = v) ∧ ¬ (a = v ∧ b = u) ∧ Dom (p b - p a) k

structure Anchored (p : Fin 8 → Fin 3 → ℝ) : Prop where
  c1 : Dom (p 1 - p 0) 0
  c2 : Dom (p 2 - p 0) 0
  c3 : Dom (p 3 - p 0) 0
  c4 : Dom (p 4 - p 0) 1
  c5 : Dom (p 5 - p 0) 1
  c6 : Dom (p 6 - p 0) 2
  c7 : Dom (p 7 - p 0) 2
  s1 : p 0 0 < p 1 0
  s2 : p 0 0 < p 2 0
  s4 : p 0 1 < p 4 1
  s6 : p 0 2 < p 6 2

theorem Dom.neg {d : ℕ} {x : Fin d → ℝ} {k : Fin d} (h : Dom x k) : Dom (-x) k := by
  intro j hj
  simpa [abs_neg] using h j hj

theorem Dom.sub_comm {d : ℕ} {a b : Fin d → ℝ} {k : Fin d} (h : Dom (a - b) k) : Dom (b - a) k := by
  have := h.neg
  rwa [neg_sub] at this

theorem Dom.unique {d : ℕ} {x : Fin d → ℝ} {k l : Fin d} (hk : Dom x k) (hl : Dom x l) : k = l := by
  by_contra hne
  have h1 := hk l (Ne.symm hne)
  have h2 := hl k hne
  linarith

theorem Dom.pos {d : ℕ} {x : Fin d → ℝ} {k : Fin d} (h : Dom x k) (j : Fin d) (hj : j ≠ k) :
    0 < |x k| :=
  lt_of_le_of_lt (abs_nonneg _) (h j hj)

end K8
