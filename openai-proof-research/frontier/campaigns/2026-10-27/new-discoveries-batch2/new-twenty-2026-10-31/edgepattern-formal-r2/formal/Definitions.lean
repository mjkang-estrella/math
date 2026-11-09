import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

namespace EdgePattern
universe u
open scoped BigOperators

structure Rooted (V : Type u) where
  graph : SimpleGraph V
  left : V
  right : V
  root_edge : graph.Adj left right

noncomputable def rootDistance {V : Type u} (P : Rooted V) (v : V) : ℕ∞ :=
  min (P.graph.edist v P.left) (P.graph.edist v P.right)

def DepthAtMost {V : Type u} (P : Rooted V) (r : ℕ) : Prop :=
  ∀ v, rootDistance P v ≤ r

def ExactDepth {V : Type u} (P : Rooted V) (r : ℕ) : Prop :=
  DepthAtMost P r ∧ ∃ v, rootDistance P v = r

noncomputable def layer {V : Type u} [Fintype V] (P : Rooted V) (i : ℕ) : Finset V :=
  by classical exact Finset.univ.filter (fun v => rootDistance P v = i)

def RegularPattern {V : Type u} [Fintype V] (P : Rooted V) (d r : ℕ) : Prop :=
  ExactDepth P r ∧ ∀ v, (P.graph.neighborSet v).ncard ≤ d ∧
    (rootDistance P v + 2 ≤ r → (P.graph.neighborSet v).ncard = d)

def GirthAtLeast {V : Type u} (P : Rooted V) (g : ℕ) : Prop :=
  ∀ v (c : P.graph.Walk v v), c.IsCycle → g ≤ c.length

def ExactGirth {V : Type u} (P : Rooted V) (g : ℕ) : Prop :=
  GirthAtLeast P g ∧ ∃ v, ∃ c : P.graph.Walk v v, c.IsCycle ∧ c.length = g

def Independent {V : Type u} (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∀ v ∈ s, ∀ w ∈ s, ¬ G.Adj v w

def Maximum {V : Type u} (G : SimpleGraph V) (s : Finset V) : Prop :=
  Independent G s ∧ ∀ t : Finset V, Independent G t → t.card ≤ s.card

noncomputable def maxima {V : Type u} [Fintype V] (G : SimpleGraph V) : Finset (Finset V) :=
  by classical exact Finset.univ.powerset.filter (Maximum G)

noncomputable def expectation {V : Type u} [Fintype V] (P : Rooted V) (i : ℕ) : ℚ :=
  by classical exact (∑ s ∈ maxima P.graph, ((s ∩ layer P i).card : ℚ)) / (maxima P.graph).card

def TreeFamily {V : Type u} [Fintype V] (P : Rooted V) (d r : ℕ) : Prop :=
  RegularPattern P d r ∧ P.graph.IsAcyclic

def Weaker {r : ℕ} (e e' : Fin (r+1) → ℝ) : Prop :=
  ∀ a : Fin (r+1) → ℚ, (∀ i, 0 < a i) →
    (∑ i, (a i : ℝ) * e' i) ≥ 1 → (∑ i, (a i : ℝ) * e i) ≥ 1

-- Both the pattern and every tree range over arbitrary finite vertex types.
def Conjecture2 : Prop :=
  ∀ (d r : ℕ), 3 ≤ d → 1 ≤ r → ∀ (V : Type u) [Fintype V] (P : Rooted V),
    RegularPattern P d r → ExactGirth P (2*r+2) →
    ∃ (m : ℕ) (W : Fin m → Type u) (f : ∀ j, Fintype (W j))
      (T : (j : Fin m) → Rooted (W j))
      (w : Fin m → ℝ),
      (∀ j, @TreeFamily (W j) (f j) (T j) d r) ∧ (∀ j, w j ∈ Set.Icc 0 1) ∧
      (∑ j, w j) = 1 ∧
      Weaker (r := r) (fun i => (expectation P i : ℝ))
        (fun i => ∑ j, w j * (@expectation (W j) (f j) (T j) i : ℝ))

end EdgePattern
