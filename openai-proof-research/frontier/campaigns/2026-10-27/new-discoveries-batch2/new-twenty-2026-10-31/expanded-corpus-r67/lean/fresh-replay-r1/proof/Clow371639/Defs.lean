import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# MathDB 371639: statement of Conjecture 7.5 of Clow–Kumar–Pragada (arXiv:2511.18747)

Literal source text (Conjecture 7.5): "There exists a constant `c > 0` such that if `G` is a graph
with `χ(G) > ω(G)` and `H` is a largest induced subgraph of `G` with `χ(H) ≤ ω(G)`, then
`χ_f(G) < c (ω(G) |V(G)| / |V(H)|)`."

Graphs are finite simple graphs.  `χ` and `ω` are Mathlib's `chromaticNumber` and `cliqueNum`.
The fractional chromatic number is the usual linear-programming value: the infimum of the total
weight of a nonnegative weighting of independent sets in which every vertex is covered with total
weight at least `1`.
-/

namespace Clow371639

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `y` is a fractional colouring of `G`: nonnegative weights on vertex sets, supported on
independent sets, such that every vertex lies in sets of total weight at least `1`. -/
def IsFractionalColoring (G : SimpleGraph V) (y : Finset V → ℝ) : Prop :=
  (∀ I, 0 ≤ y I) ∧ (∀ I, y I ≠ 0 → G.IsIndepSet (I : Set V)) ∧
    ∀ v, 1 ≤ ∑ I ∈ univ.filter (fun I : Finset V => v ∈ I), y I

/-- The fractional chromatic number `χ_f(G)`: the least total weight of a fractional colouring. -/
noncomputable def fracChromaticNumber (G : SimpleGraph V) : ℝ :=
  sInf {r : ℝ | ∃ y : Finset V → ℝ, IsFractionalColoring G y ∧ ∑ I, y I = r}

/-- `|V(H)|` for a largest induced subgraph `H` of `G` with `χ(H) ≤ ω(G)`. -/
noncomputable def largestLowChromaticOrder (G : SimpleGraph V) : ℕ :=
  sSup {m : ℕ | ∃ s : Finset V, s.card = m ∧
    (G.induce (s : Set V)).chromaticNumber ≤ (G.cliqueNum : ℕ∞)}

/-- Conjecture 7.5 of arXiv:2511.18747 (MathDB 371639), over all finite simple graphs. -/
def Conjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    (G.cliqueNum : ℕ∞) < G.chromaticNumber →
      fracChromaticNumber G <
        c * ((G.cliqueNum : ℝ) * (Fintype.card V : ℝ) / (largestLowChromaticOrder G : ℝ))

end Clow371639
