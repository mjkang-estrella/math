/-
# Bunkbed E7: finite-counting layer

Token-universe instances, the two domain splits, the uniform pin rule, the prefix
state, the transition kernel and the reflection-dominance step.  Pure finite
combinatorics over `Nat` and `Int`; no probability, no measure theory.
-/
import BunkbedBase
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Intervals

namespace Bun

open Finset

/-! ### Universes -/

instance {n : Nat} : Fintype {p : Fin n × Fin n // (p.1 : Nat) < (p.2 : Nat)} :=
  Subtype.fintype (fun p : Fin n × Fin n => (p.1 : Nat) < (p.2 : Nat))

def htokenEquiv (n : Nat) : HToken n ≃ {p : Fin n × Fin n // (p.1 : Nat) < (p.2 : Nat)} × Bool :=
  ⟨fun t => (⟨(t.fst, t.snd), t.hlt⟩, t.layer),
   fun p => ⟨p.1.1.1, p.1.1.2, p.1.2, p.2⟩,
   fun t => by obtain ⟨i, j, h, l⟩ := t; simp,
   fun p => by
     obtain ⟨q, l⟩ := p
     have hq : q = ⟨(q.1.1, q.1.2), q.2⟩ := Subtype.ext rfl
     rw [hq]⟩

instance {n : Nat} : Fintype (HToken n) := Fintype.ofEquiv _ (htokenEquiv n).symm

instance : Fintype (Token n) := by unfold Token; infer_instance

noncomputable instance {n : Nat} : Fintype (Out n) := by
  classical
  unfold Out
  infer_instance

end Bun
