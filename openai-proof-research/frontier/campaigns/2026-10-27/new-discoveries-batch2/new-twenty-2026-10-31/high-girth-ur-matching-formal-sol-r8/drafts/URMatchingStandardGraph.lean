module
public import URMatchingSurvivorGraph
public import URMatchingBase
public import Mathlib.Combinatorics.SimpleGraph.Finite
@[expose] public section
namespace URMatching
universe u
variable {V : Type u}

theorem inducedGraph_eq_induce (G : SimpleGraph V) (P : Set V) :
    inducedGraph G P = G.induce P := by
  ext u v
  rfl

theorem degreeBound_iff_standard [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (d : ℕ) :
    DegreeBound G d ↔ ∀ v, G.degree v ≤ d := by
  have he (v : V) : G.degree v = (@Finset.filter V (G.Adj v) (fun a => Classical.propDecidable _) Finset.univ).card := by
    unfold SimpleGraph.degree
    apply congrArg Finset.card
    ext w
    simp
  constructor
  · intro hd v
    rw [he]
    exact hd v
  · intro hd v
    have hv := hd v
    rw [he] at hv
    exact hv
end URMatching
