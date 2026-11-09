import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Aesop

open scoped BigOperators
namespace Adverse381433

abbrev Cell := ZMod 6 × ZMod 6

def latinGraph : SimpleGraph Cell where
  Adj p q := p ≠ q ∧ (p.1 = q.1 ∨ p.2 = q.2 ∨ p.1 + p.2 = q.1 + q.2)
  symm := ⟨by intro p q h; exact ⟨Ne.symm h.1, h.2.imp Eq.symm (fun h => h.imp Eq.symm Eq.symm)⟩⟩
  loopless := ⟨by intro p; simp⟩

noncomputable def adjacency {V : Type} [Fintype V] (G : SimpleGraph V) :
    Matrix V V ℝ := by
  classical
  exact fun i j => if G.Adj i j then 1 else 0

noncomputable def realEigenvalues {V : Type} [Fintype V] (G : SimpleGraph V) : Set ℝ :=
  {μ | ∃ z : V → ℝ, z ≠ 0 ∧ (adjacency G).mulVec z = μ • z}

noncomputable def leastEigenvalue {V : Type} [Fintype V] (G : SimpleGraph V) : ℝ :=
  sInf (realEigenvalues G)

noncomputable def objective {V : Type} [Fintype V] (G : SimpleGraph V) (x : V → ℝ) : ℝ := by
  classical
  exact 2 * ∑ i, x i - ∑ i, ∑ j,
    x i * ((adjacency G i j / (-leastEigenvalue G)) + if i = j then 1 else 0) * x j

noncomputable def upsilon {V : Type} [Fintype V] (G : SimpleGraph V) : ℝ :=
  sSup {r | ∃ x : V → ℝ, (∀ i, 0 ≤ x i) ∧ r = objective G x}

def Independent {V : Type} (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ¬G.Adj a b

noncomputable def alpha {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sSup {n | ∃ s : Finset V, Independent G s ∧ s.card = n}

abbrev deletionVertices {V : Type} (G : SimpleGraph V) (v : V) := {w : V // ¬G.Adj v w}

noncomputable instance {V : Type} [Fintype V] (G : SimpleGraph V) (v : V) :
    Fintype (deletionVertices G v) := by
  classical
  unfold deletionVertices
  infer_instance

def deleteOpen {V : Type} (G : SimpleGraph V) (v : V) : SimpleGraph (deletionVertices G v) :=
  G.induce {w | ¬G.Adj v w}

noncomputable def Adverse {V : Type} [Fintype V] (G : SimpleGraph V) : Prop := by
  classical
  exact (∀ v, ∃ w, G.Adj v w) ∧ (∃ k : ℤ, upsilon G = k) ∧
    (∃ k : ℤ, leastEigenvalue G = k) ∧
    ∀ v, upsilon (deleteOpen G v) = upsilon G ∧
      leastEigenvalue (deleteOpen G v) = leastEigenvalue G

noncomputable def QGraph {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  (alpha G : ℝ) = upsilon G

noncomputable def CardosoLuzConjecture : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), Adverse G → QGraph G

end Adverse381433
