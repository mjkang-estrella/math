import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases
set_option autoImplicit false
namespace SteinerReflection
open SimpleGraph
abbrev V := Fin 30
def leaves : Finset V := Finset.univ.erase 0
/-- Edge j labels the undirected edge {0,j}; unused isolated vertices do not count. -/
def edgeGraph (E : Finset V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ((u = 0 ∧ v ∈ E) ∨ (v = 0 ∧ u ∈ E))
  symm := ⟨by intro u v h; exact ⟨Ne.symm h.1,h.2.symm⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩
lemma edgeGraph_le (E : Finset V) : edgeGraph E ≤ starGraph (0:V) := by
  intro u v h; exact starGraph_adj.mpr ⟨h.1,h.2.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)⟩
theorem star_tree : (starGraph (0:V)).IsTree := isTree_starGraph 0
/-- A spanning edge subset connects the terminals if every pair is joined by a finite walk.
Its terminal component is a connected subgraph containing the terminals. -/
def Feasible (t : Fin 4 → V) (E : Finset V) : Prop :=
  E ⊆ leaves ∧ ∀ a b, (edgeGraph E).Reachable (t a) (t b)
noncomputable def required (t : Fin 4 → V) : Finset V := by
  classical
  exact leaves.filter fun j => (∃ a, t a = j) ∧ (∃ b, t b ≠ j)
lemma required_mem (t : Fin 4 → V) (j : V) :
    j ∈ required t ↔ j ≠ 0 ∧ (∃ a, t a = j) ∧ (∃ b, t b ≠ j) := by
  classical
  simp [required,leaves]
lemma required_feasible (t : Fin 4 → V) : Feasible t (required t) := by
  classical
  refine ⟨Finset.filter_subset _ _,fun a b => ?_⟩
  by_cases hab : t a = t b
  · rw [hab]
  have hr (c : Fin 4) (e : Fin 4) (h : t c ≠ t e) :
      (edgeGraph (required t)).Reachable (t c) 0 := by
    by_cases hc : t c = 0
    · rw [hc]
    · apply Adj.reachable
      exact ⟨hc,Or.inr ⟨rfl,(required_mem t (t c)).mpr ⟨hc,⟨c,rfl⟩,⟨e,Ne.symm h⟩⟩⟩⟩
  exact (hr a b hab).trans (hr b a (Ne.symm hab)).symm
lemma required_subset (t : Fin 4 → V) (E : Finset V) (hE : Feasible t E) :
    required t ⊆ E := by
  intro j hj
  obtain ⟨hj0,⟨a,ha⟩,⟨b,hb⟩⟩ := (required_mem t j).mp hj
  have hr := hE.2 a b
  rw [ha] at hr
  obtain ⟨v,hv⟩ := hr.nonempty_neighborSet_left (Ne.symm hb)
  exact hv.2.elim (fun h => (hj0 h.1).elim) (fun h => h.2)
lemma feasible_nonempty (t : Fin 4 → V) : ∃ n : ℕ, ∃ E, Feasible t E ∧ E.card = n :=
  ⟨(required t).card, required t, required_feasible t,rfl⟩
/-- Literal minimum number of edges among all star edge-subgraphs joining the ordered terminals. -/
noncomputable def minimumDistance (t : Fin 4 → V) : ℕ := by
  classical
  exact Nat.find (feasible_nonempty t)
theorem minimumDistance_eq (t : Fin 4 → V) : minimumDistance t = (required t).card := by
  classical
  apply Nat.le_antisymm
  · exact Nat.find_min' (feasible_nonempty t) ⟨required t,required_feasible t,rfl⟩
  · obtain ⟨E,hE,hcard⟩ := Nat.find_spec (feasible_nonempty t)
    change (required t).card ≤ Nat.find (feasible_nonempty t)
    rw [← hcard]
    exact Finset.card_le_card (required_subset t E hE)
/-- Nonvacuity of the minimum and a minimizing actual edge-subgraph. -/
theorem minimum_attained (t : Fin 4 → V) :
    ∃ E, Feasible t E ∧ E.card = minimumDistance t ∧
      ∀ F, Feasible t F → E.card ≤ F.card := by
  refine ⟨required t,required_feasible t,(minimumDistance_eq t).symm,?_⟩
  intro F hF; exact Finset.card_le_card (required_subset t F hF)
end SteinerReflection
