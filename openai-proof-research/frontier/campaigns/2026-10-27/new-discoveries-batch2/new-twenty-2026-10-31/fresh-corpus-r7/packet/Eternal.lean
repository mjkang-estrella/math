import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Nat.Find
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fin.VecNotation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace Eternal
abbrev Graph (n : ℕ) := SimpleGraph (Fin n)
abbrev Cover {n} (G : Graph n) (c : Finset (Fin n)) : Prop :=
  ∀ u v, G.Adj u v → u ∈ c ∨ v ∈ c
abbrev Transport {n} (G : Graph n) (c d : Finset (Fin n)) (u v : Fin n)
    (f : Fin n → Fin n) : Prop :=
  Set.InjOn f ↑c ∧ c.image f = d ∧
  (∀ x ∈ c, f x = x ∨ G.Adj x (f x)) ∧
  ((u ∈ c ∧ f u = v) ∨ (v ∈ c ∧ f v = u))
def Defends {n} (G : Graph n) (k : ℕ) : Prop :=
  ∃ S : Set (Finset (Fin n)), S.Nonempty ∧ ∀ c ∈ S,
    c.card = k ∧ Cover G c ∧ ∀ u v, G.Adj u v →
      ∃ d ∈ S, ∃ f, Transport G c d u v f
noncomputable def number {n} (G : Graph n) : ℕ := by
  classical
  exact if h : ∃ k, Defends G k then Nat.find h else 0

def large : Graph 8 where
  Adj u v := u ≠ v ∧ ((u.val < 4 ∧ v.val < 4) ∨
    (u.val < 4 ∧ 4 ≤ v.val ∧ u.val / 2 = (v.val - 4) / 2) ∨
    (v.val < 4 ∧ 4 ≤ u.val ∧ v.val / 2 = (u.val - 4) / 2))
  symm := ⟨by intro u v h; exact ⟨Ne.symm h.1, h.2.elim (fun a => Or.inl ⟨a.2,a.1⟩)
    (fun a => a.elim (fun b => Or.inr (Or.inr b)) (fun b => Or.inr (Or.inl b)))⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩
instance : DecidableRel large.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
def diamond : Graph 4 where
  Adj u v := u ≠ v ∧ (u.val < 2 ∨ v.val < 2)
  symm := ⟨by intro u v h; exact ⟨Ne.symm h.1, h.2.symm⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩
instance : DecidableRel diamond.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
def cfg (s : Fin 4) : Finset (Fin 8) := {0,1,2,3, ⟨s.val+4, by omega⟩}
def nextState : Fin 4 → Fin 8 → Fin 8 → Fin 4 :=
![![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 2, 3], ![0, 0, 0, 0, 0, 0, 2, 3], ![0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 2, 2, 0, 0, 0, 0], ![0, 0, 3, 3, 0, 0, 0, 0]], ![![1, 0, 0, 0, 0, 0, 1, 1], ![0, 1, 0, 0, 0, 0, 1, 1], ![0, 0, 1, 0, 1, 1, 2, 3], ![0, 0, 0, 1, 1, 1, 2, 3], ![0, 0, 1, 1, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 1, 1, 1], ![1, 1, 2, 2, 1, 1, 1, 1], ![1, 1, 3, 3, 1, 1, 1, 1]], ![![2, 0, 0, 0, 0, 1, 2, 2], ![0, 2, 0, 0, 0, 1, 2, 2], ![0, 0, 2, 0, 2, 2, 0, 3], ![0, 0, 0, 2, 2, 2, 0, 3], ![0, 0, 2, 2, 2, 2, 2, 2], ![1, 1, 2, 2, 2, 2, 2, 2], ![2, 2, 0, 0, 2, 2, 2, 2], ![2, 2, 3, 3, 2, 2, 2, 2]], ![![3, 0, 0, 0, 0, 1, 3, 3], ![0, 3, 0, 0, 0, 1, 3, 3], ![0, 0, 3, 0, 3, 3, 2, 0], ![0, 0, 0, 3, 3, 3, 2, 0], ![0, 0, 3, 3, 3, 3, 3, 3], ![1, 1, 3, 3, 3, 3, 3, 3], ![3, 3, 2, 2, 3, 3, 3, 3], ![3, 3, 0, 0, 3, 3, 3, 3]]]

def response : Fin 4 → Fin 8 → Fin 8 → Fin 8 → Fin 8 :=
![![![![0, 1, 2, 3, 4, 5, 6, 7], ![1, 0, 2, 3, 4, 5, 6, 7], ![1, 2, 0, 3, 4, 5, 6, 7], ![1, 2, 3, 0, 4, 5, 6, 7], ![1, 4, 2, 3, 0, 5, 6, 7], ![5, 0, 2, 3, 1, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]], ![![1, 0, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 2, 1, 3, 4, 5, 6, 7], ![0, 2, 3, 1, 4, 5, 6, 7], ![0, 4, 2, 3, 1, 5, 6, 7], ![0, 5, 2, 3, 1, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]], ![![1, 2, 0, 3, 4, 5, 6, 7], ![0, 2, 1, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 3, 2, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 2, 6, 3, 1, 5, 6, 7], ![0, 2, 7, 3, 1, 5, 6, 7]], ![![1, 2, 3, 0, 4, 5, 6, 7], ![0, 2, 3, 1, 4, 5, 6, 7], ![0, 1, 3, 2, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 2, 3, 6, 1, 5, 6, 7], ![0, 2, 3, 7, 1, 5, 6, 7]], ![![1, 4, 2, 3, 0, 5, 6, 7], ![0, 4, 2, 3, 1, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]], ![![5, 0, 2, 3, 1, 5, 6, 7], ![0, 5, 2, 3, 1, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]], ![![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 2, 6, 3, 1, 5, 6, 7], ![0, 2, 3, 6, 1, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]], ![![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 2, 7, 3, 1, 5, 6, 7], ![0, 2, 3, 7, 1, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]], ![![![0, 1, 2, 3, 4, 5, 6, 7], ![1, 4, 2, 3, 4, 0, 6, 7], ![2, 4, 0, 3, 4, 1, 6, 7], ![2, 4, 3, 0, 4, 1, 6, 7], ![4, 0, 2, 3, 4, 1, 6, 7], ![1, 4, 2, 3, 4, 0, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]], ![![1, 4, 2, 3, 4, 0, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![2, 4, 1, 3, 4, 0, 6, 7], ![2, 4, 3, 1, 4, 0, 6, 7], ![0, 4, 2, 3, 4, 1, 6, 7], ![0, 4, 2, 3, 4, 1, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]], ![![2, 4, 0, 3, 4, 1, 6, 7], ![2, 4, 1, 3, 4, 0, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 4, 3, 2, 4, 1, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 2, 6, 3, 4, 1, 6, 7], ![0, 2, 7, 3, 4, 1, 6, 7]], ![![2, 4, 3, 0, 4, 1, 6, 7], ![2, 4, 3, 1, 4, 0, 6, 7], ![0, 4, 3, 2, 4, 1, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 2, 3, 6, 4, 1, 6, 7], ![0, 2, 3, 7, 4, 1, 6, 7]], ![![4, 0, 2, 3, 4, 1, 6, 7], ![0, 4, 2, 3, 4, 1, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]], ![![1, 4, 2, 3, 4, 0, 6, 7], ![0, 4, 2, 3, 4, 1, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]], ![![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 2, 6, 3, 4, 1, 6, 7], ![0, 2, 3, 6, 4, 1, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]], ![![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 2, 7, 3, 4, 1, 6, 7], ![0, 2, 3, 7, 4, 1, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]], ![![![0, 1, 2, 3, 4, 5, 6, 7], ![1, 4, 0, 2, 4, 5, 3, 7], ![1, 4, 0, 2, 4, 5, 3, 7], ![1, 4, 2, 0, 4, 5, 3, 7], ![4, 0, 1, 2, 4, 5, 3, 7], ![5, 0, 1, 2, 4, 5, 3, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]], ![![1, 4, 0, 2, 4, 5, 3, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 4, 1, 2, 4, 5, 3, 7], ![0, 4, 2, 1, 4, 5, 3, 7], ![0, 4, 1, 2, 4, 5, 3, 7], ![0, 5, 1, 2, 4, 5, 3, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]], ![![1, 4, 0, 2, 4, 5, 3, 7], ![0, 4, 1, 2, 4, 5, 3, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 4, 1, 2, 4, 5, 3, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 4, 1, 3, 4, 5, 2, 7], ![0, 1, 7, 2, 4, 5, 3, 7]], ![![1, 4, 2, 0, 4, 5, 3, 7], ![0, 4, 2, 1, 4, 5, 3, 7], ![0, 4, 1, 2, 4, 5, 3, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 4, 1, 2, 4, 5, 3, 7], ![0, 1, 2, 7, 4, 5, 3, 7]], ![![4, 0, 1, 2, 4, 5, 3, 7], ![0, 4, 1, 2, 4, 5, 3, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]], ![![5, 0, 1, 2, 4, 5, 3, 7], ![0, 5, 1, 2, 4, 5, 3, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]], ![![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 4, 1, 3, 4, 5, 2, 7], ![0, 4, 1, 2, 4, 5, 3, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]], ![![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 7, 2, 4, 5, 3, 7], ![0, 1, 2, 7, 4, 5, 3, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]], ![![![0, 1, 2, 3, 4, 5, 6, 7], ![1, 4, 0, 2, 4, 5, 6, 3], ![1, 4, 0, 2, 4, 5, 6, 3], ![1, 4, 2, 0, 4, 5, 6, 3], ![4, 0, 1, 2, 4, 5, 6, 3], ![5, 0, 1, 2, 4, 5, 6, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]], ![![1, 4, 0, 2, 4, 5, 6, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 4, 1, 2, 4, 5, 6, 3], ![0, 4, 2, 1, 4, 5, 6, 3], ![0, 4, 1, 2, 4, 5, 6, 3], ![0, 5, 1, 2, 4, 5, 6, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]], ![![1, 4, 0, 2, 4, 5, 6, 3], ![0, 4, 1, 2, 4, 5, 6, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 4, 1, 2, 4, 5, 6, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 6, 2, 4, 5, 6, 3], ![0, 4, 1, 3, 4, 5, 6, 2]], ![![1, 4, 2, 0, 4, 5, 6, 3], ![0, 4, 2, 1, 4, 5, 6, 3], ![0, 4, 1, 2, 4, 5, 6, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 6, 4, 5, 6, 3], ![0, 4, 1, 2, 4, 5, 6, 3]], ![![4, 0, 1, 2, 4, 5, 6, 3], ![0, 4, 1, 2, 4, 5, 6, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]], ![![5, 0, 1, 2, 4, 5, 6, 3], ![0, 5, 1, 2, 4, 5, 6, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]], ![![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 6, 2, 4, 5, 6, 3], ![0, 1, 2, 6, 4, 5, 6, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]], ![![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 4, 1, 3, 4, 5, 6, 2], ![0, 4, 1, 2, 4, 5, 6, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]]]

theorem cfg_spec : ∀ s, (cfg s).card = 5 ∧ Cover large (cfg s) := by decide

theorem response_spec : ∀ s u v, large.Adj u v →
    Transport large (cfg s) (cfg (nextState s u v)) u v (response s u v) := by
  decide

theorem large_defends : Defends large 5 := by
  refine ⟨Set.range cfg, ⟨cfg 0, ⟨0,rfl⟩⟩, ?_⟩
  rintro c ⟨s,rfl⟩
  refine ⟨(cfg_spec s).1, (cfg_spec s).2, ?_⟩
  intro u v h
  exact ⟨cfg (nextState s u v), ⟨nextState s u v,rfl⟩, response s u v,
    response_spec s u v h⟩

theorem small_cover : ∀ c : Finset (Fin 4), c.card ≤ 2 → Cover diamond c → c = {0,1} := by
  decide

theorem diamond_lower {k : ℕ} (h : Defends diamond k) : 3 ≤ k := by
  by_contra hk
  obtain ⟨S, ⟨c,hc⟩, hs⟩ := h
  have hcs := hs c hc
  have heq : c = {0,1} := small_cover c (by omega) hcs.2.1
  obtain ⟨d,hd,f,hf⟩ := hcs.2.2 0 2 (by decide)
  have hdeq : d = {0,1} := small_cover d (by have := (hs d hd).1; omega) (hs d hd).2.1
  have h2 : (2 : Fin 4) ∈ d := by
    rcases hf.2.2.2 with ha | ha
    · rw [← hf.2.1, ← ha.2]; exact Finset.mem_image.mpr ⟨0,ha.1,rfl⟩
    · simp [heq] at ha
  simp [hdeq] at h2

theorem full_defends {n} (G : Graph n) : Defends G n := by
  classical
  refine ⟨{Finset.univ}, ⟨Finset.univ, rfl⟩, ?_⟩
  intro c hc
  have heq : c = Finset.univ := hc
  subst c
  refine ⟨by simp, ?_, ?_⟩
  · intro u v _; simp
  · intro u v huv
    refine ⟨Finset.univ, rfl, Equiv.swap u v, ?_, ?_, ?_, ?_⟩
    · exact (Equiv.swap u v).injective.injOn
    · exact Finset.image_univ_of_surjective (Equiv.swap u v).surjective
    · intro x _
      by_cases hxu : x = u
      · subst x; exact Or.inr (by simpa using huv)
      · by_cases hxv : x = v
        · subst x; exact Or.inr (by simpa using huv.symm)
        · exact Or.inl (Equiv.swap_apply_of_ne_of_ne hxu hxv)
    · exact Or.inl ⟨by simp, by simp⟩

 theorem number_defends {n} (G : Graph n) : Defends G (number G) := by
  classical
  have h : ∃ k, Defends G k := ⟨n, full_defends G⟩
  simp only [number, dite_eq_left h]
  exact Nat.find_spec h

theorem number_le {n} {G : Graph n} {k} (hk : Defends G k) : number G ≤ k := by
  classical
  have h : ∃ k, Defends G k := ⟨k,hk⟩
  simp only [number, dite_eq_left h]
  exact Nat.find_min' h hk

theorem diamond_defends : Defends diamond 3 := by
  refine ⟨{c | c.card = 3}, ?_, ?_⟩
  · exact ⟨{0,1,2}, by decide⟩
  · intro c hc
    refine ⟨hc, ?_, ?_⟩
    · have h : ∀ c : Finset (Fin 4), c.card = 3 → Cover diamond c := by decide
      exact h c hc
    · have h : ∀ c : Finset (Fin 4), c.card = 3 → ∀ u v, diamond.Adj u v →
          ∃ d : Finset (Fin 4), d.card = 3 ∧ ∃ f, Transport diamond c d u v f := by decide
      exact h c hc

theorem large_number_le : number large ≤ 5 := number_le large_defends

theorem diamond_number_ge : 3 ≤ number diamond := by
  classical
  have h : ∃ k, Defends diamond k := ⟨3, diamond_defends⟩
  simp only [number, dite_eq_left h]
  exact diamond_lower (Nat.find_spec h)
/-- A closed family yields a legal infinite response to every infinite attack sequence. -/
theorem infinite_response {n k} {G : Graph n} (h : Defends G k)
    (a b : ℕ → Fin n) (legal : ∀ t, G.Adj (a t) (b t)) :
    ∃ c : ℕ → Finset (Fin n), ∀ t, (c t).card = k ∧ Cover G (c t) ∧
      ∃ f, Transport G (c t) (c (t+1)) (a t) (b t) f := by
  classical
  obtain ⟨S, ⟨c0,h0⟩, hs⟩ := h
  let step (c : {c // c ∈ S}) (t : ℕ) : {c // c ∈ S} :=
    ⟨Classical.choose ((hs c.val c.property).2.2 (a t) (b t) (legal t)),
      (Classical.choose_spec ((hs c.val c.property).2.2 (a t) (b t) (legal t))).1⟩
  let state : ℕ → {c // c ∈ S} := Nat.rec ⟨c0,h0⟩ (fun t c => step c t)
  refine ⟨fun t => (state t).val, fun t => ?_⟩
  refine ⟨(hs (state t).val (state t).property).1,
    (hs (state t).val (state t).property).2.1, ?_⟩
  exact (Classical.choose_spec
    ((hs (state t).val (state t).property).2.2 (a t) (b t) (legal t))).2

abbrev MinDegreeTwo {n} (G : Graph n) : Prop :=
  ∀ u, ∃ v w, v ≠ w ∧ G.Adj u v ∧ G.Adj u w

def leftEmbedding : Fin 4 → Fin 8 := ![0,1,4,5]
def rightEmbedding : Fin 4 → Fin 8 := ![2,3,6,7]

def SourceClaim : Prop := ∀ n m l (G : Graph n) (H : Graph m) (K : Graph l)
    (e : Fin m → Fin n) (f : Fin l → Fin n),
  G.Connected → Function.Injective e → Function.Injective f →
  (∀ u v, e u ≠ f v) → (∀ x, (∃ u, e u = x) ∨ (∃ v, f v = x)) →
  (∀ u v, H.Adj u v → G.Adj (e u) (e v)) →
  (∀ u v, K.Adj u v ↔ G.Adj (f u) (f v)) →
  MinDegreeTwo H → MinDegreeTwo K → number H + number K ≤ number G

theorem large_connected : large.Connected := by
  refine ⟨?_⟩
  have root : ∀ u : Fin 8, large.Reachable u 0 := by
    intro u
    have h : ∀ u : Fin 8, u = 0 ∨ large.Adj u 0 ∨
        ∃ w, large.Adj u w ∧ large.Adj w 0 := by decide
    rcases h u with heq | hadj | ⟨w, huw, hwv⟩
    · subst u; exact SimpleGraph.Reachable.refl 0
    · exact hadj.reachable
    · exact huw.reachable.trans hwv.reachable
  intro u v
  exact (root u).trans (root v).symm

theorem exact_source_refuted : ¬ SourceClaim := by
  intro h
  have bad := h 8 4 4 large diamond diamond leftEmbedding rightEmbedding
    large_connected (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have lo := diamond_number_ge
  have hi := large_number_le
  omega

#print axioms full_defends
#print axioms number_defends
#print axioms infinite_response
#print axioms exact_source_refuted
#print axioms large_defends
#print axioms diamond_lower
#print axioms diamond_defends
end Eternal
