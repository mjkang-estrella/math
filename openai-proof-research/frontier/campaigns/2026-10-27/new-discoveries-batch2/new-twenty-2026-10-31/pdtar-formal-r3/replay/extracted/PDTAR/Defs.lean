import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic

namespace PDTAR
open Finset
open scoped symmDiff
variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def closed (G : SimpleGraph V) (S : Finset V) : Finset V := by
  classical
  exact univ.filter fun u => u ∈ S ∨ ∃ v ∈ S, G.Adj v u

noncomputable def step (G : SimpleGraph V) (O : Finset V) : Finset V := by
  classical
  exact univ.filter fun u => u ∈ O ∨ ∃ v ∈ O, G.Adj v u ∧
    ∀ w, G.Adj v w → w ∉ O → w = u

noncomputable def propagate (G : SimpleGraph V) (O : Finset V) : ℕ → Finset V
  | 0 => O
  | n + 1 => step G (propagate G O n)

noncomputable def obs (G : SimpleGraph V) (S : Finset V) : ℕ → Finset V
  | 0 => S
  | n + 1 => propagate G (closed G S) n

def IsPD (G : SimpleGraph V) (S : Finset V) : Prop := ∃ n, obs G S n = univ

/-- No outside vertex has exactly one neighbour in the nonempty fort. -/
def IsFort (G : SimpleGraph V) (F : Finset V) : Prop :=
  F.Nonempty ∧ ∀ v, v ∉ F → ∀ u ∈ F, G.Adj v u →
    ∃ w ∈ F, w ≠ u ∧ G.Adj v w

def NoIsolated (G : SimpleGraph V) : Prop := ∀ v, ∃ w, G.Adj v w

noncomputable def tar (G : SimpleGraph V) : SimpleGraph {S : Finset V // IsPD G S} where
  Adj S T := (S.val ∆ T.val).card = 1
  symm := ⟨by intros S T h; simpa [symmDiff_comm] using h⟩
  loopless := ⟨by intro S; simp⟩

/-- Quantifies over every finite graph, with no restriction on its order. -/
def TARUnique (G : SimpleGraph V) : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W),
    NoIsolated H → Nonempty (tar H ≃g tar G) → Nonempty (H ≃g G)

@[simp] theorem mem_closed (G : SimpleGraph V) (S : Finset V) (u : V) :
    u ∈ closed G S ↔ u ∈ S ∨ ∃ v ∈ S, G.Adj v u := by
  classical
  simp [closed]

@[simp] theorem mem_step (G : SimpleGraph V) (O : Finset V) (u : V) :
    u ∈ step G O ↔ u ∈ O ∨ ∃ v ∈ O, G.Adj v u ∧
      ∀ w, G.Adj v w → w ∉ O → w = u := by
  classical
  simp [step]
end PDTAR
