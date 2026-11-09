module
public import URMatchingBase
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Basic.Real.Basic
@[expose] public section
namespace URMatching
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
/-- Every genuine simple cycle has length at least g; forests satisfy this for all g. -/
def GirthAtLeast (G : SimpleGraph V) (g : ℕ) : Prop :=
  ∀ v : V, ∀ p : G.Walk v v, p.IsCycle → g ≤ p.length

/-- Full source class in any fixed universe, not merely bipartite or Fin-labelled graphs. -/
def SourceConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ Δ : ℕ, 0 < Δ → ∃ g : ℕ, 0 < g ∧
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      DegreeBound G Δ → GirthAtLeast G g →
        (1 - ε) * (matchingNumber G : ℝ) ≤ (urMatchingNumber G : ℝ)

end URMatching
