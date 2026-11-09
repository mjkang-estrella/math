/-
MathDB 352972: balanced-graph conjecture for flat graphs -- literal refutation.

Source: Hossein Teimoori Faal, "On Clique Roots of Flat Graphs", arXiv:2112.09721v1.
Definition 2.2 (p4): flat = every edge lies in at most two triangles (3-cliques).
Conjecture 2 (p6): every flat graph is balanced, i.e. the absolute difference
between the odd-clique count sum and the even-clique count sum is at most 1
(c_0 = 1 is counted among the even cliques).

Endpoint: refutation of the universal statement over ALL finite simple graphs,
by the finite simple graph K_{3,3}: flat, yet discrepancy 4 > 1 with c_0
(and 3 > 1 under the positive-index convention).

Pins: Lean v4.34.1 (5045d0056413266e57c625dcd7c365b10e377c52),
mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.NatAbs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# MathDB 352972: balanced-graph conjecture for flat graphs, literal refutation

Universal endpoint: `NOT (for all finite simple graphs G, flat G -> balanced G)`,
witnessed by `K_{3,3}` with clique-count discrepancy 4 > 1 (c_0 = 1 convention)
and 3 > 1 (positive-index convention).
-/

open BigOperators

namespace FlatBalance

/-! ## Simple graphs -/

/-- A simple undirected graph: irreflexive symmetric adjacency (no loops,
undirected).  Finiteness is carried by a `Fintype` instance on the vertex
type, never by the structure itself. -/
structure SimpleGraph (V : Type) where
  /-- The adjacency relation. -/
  Adj : V → V → Prop
  /-- Adjacency is symmetric. -/
  adj_symm : ∀ a b, Adj a b → Adj b a
  /-- Adjacency is irreflexive. -/
  adj_irrefl : ∀ a, ¬ Adj a a

/-! ## Cliques, triangles, counts, flatness, balance

The data-level definitions below use classical decidability for the
clique/triangle predicates; this contributes at most the axiom
`Classical.choice`, which is on the allowed list. -/

open Classical

/-- `s` is a clique of `G`: all its vertices are pairwise adjacent. -/
def IsClique {V : Type} (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, a ≠ b → G.Adj a b

/-- The set of `k`-cliques: `k`-element vertex subsets which are cliques.
This is `c_k(G)` as a Finset; every subset of the vertex type is eligible
since it is automatically a subset of `univ`. -/
noncomputable def cliqueFinset {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    Finset (Finset V) :=
  ((Finset.univ : Finset V).powerset).filter fun s => s.card = k ∧ IsClique G s

/-- The number `c_k(G)` of `k`-cliques of `G`. -/
noncomputable def cliqueCount {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) : ℕ :=
  (cliqueFinset G k).card

/-- Membership characterization of the `k`-clique set. -/
theorem mem_cliqueFinset {V : Type} [Fintype V] {G : SimpleGraph V} {s : Finset V} {k : ℕ} :
    s ∈ cliqueFinset G k ↔ s.card = k ∧ IsClique G s := by
  simp only [cliqueFinset, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ,
    true_and]

/-- A triangle of `G`: a three-element clique, exactly the source's notion of
a triangle (3-clique) on which edge-incidence is counted. -/
def IsTriangle {V : Type} (G : SimpleGraph V) (s : Finset V) : Prop :=
  s.card = 3 ∧ IsClique G s

/-- The Finset of triangles of `G` containing both `a` and `b`:
the edge-in-triangle incidence set of source Definition 2.2. -/
noncomputable def triangleSet {V : Type} [Fintype V] (G : SimpleGraph V) (a b : V) :
    Finset (Finset V) :=
  ((Finset.univ : Finset V).powerset).filter fun s => IsTriangle G s ∧ a ∈ s ∧ b ∈ s

/-- The common neighbours of `a` and `b`. -/
noncomputable def commonNbrFinset {V : Type} [Fintype V] (G : SimpleGraph V) (a b : V) :
    Finset V :=
  Finset.univ.filter fun c => G.Adj a c ∧ G.Adj b c

/-- Flatness, source Definition 2.2: every edge lies in at most two triangles.
No planarity, connectedness or no-isolated-edge condition is imposed. -/
noncomputable def Flat {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ a b, G.Adj a b → (triangleSet G a b).card ≤ 2

/-- The sum of the `c_k(G)` over odd `k`, up to the vertex count. -/
noncomputable def oddCliqueSum {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  ∑ d ∈ Finset.range (Fintype.card V + 1), if d % 2 = 1 then cliqueCount G d else 0

/-- The sum of the `c_k(G)` over even `k` *including* `k = 0` (source
convention `c_0 = 1`), up to the vertex count. -/
noncomputable def evenCliqueSum {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  ∑ d ∈ Finset.range (Fintype.card V + 1), if d % 2 = 0 then cliqueCount G d else 0

/-- The sum over even `k ≥ 1` only (positive-index convention, no `c_0`). -/
noncomputable def evenCliqueSumPos {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  ∑ d ∈ Finset.range (Fintype.card V + 1),
    if d % 2 = 0 ∧ 0 < d then cliqueCount G d else 0

/-- The clique-count discrepancy `D_clique(G)` of the source, equation (14):
the absolute value of the difference of the odd and even sums, as a
natural number via `Int.natAbs` (the exact absolute value on Z). -/
noncomputable def discrepancyNat {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  Int.natAbs ((oddCliqueSum G : ℤ) - (evenCliqueSum G : ℤ))

/-- The discrepancy under the positive-index convention (no `c_0`). -/
noncomputable def discrepancyNatPos {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  Int.natAbs ((oddCliqueSum G : ℤ) - (evenCliqueSumPos G : ℤ))

/-- Balanced: `D_clique(G) ≤ 1`. -/
noncomputable def Balanced {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  discrepancyNat G ≤ 1

/-! ## The witness K_{3,3} -/

/-- Adjacency of the witness: vertices are adjacent iff they lie in different
summands of `Fin 3 ⊕ Fin 3`. -/
def K33Adj : Fin 3 ⊕ Fin 3 → Fin 3 ⊕ Fin 3 → Prop
  | Sum.inl _, Sum.inr _ => True
  | Sum.inr _, Sum.inl _ => True
  | _, _ => False

/-- The witness graph `K_{3,3}`: two disjoint three-element sides, all and
only cross edges.  A genuine finite simple graph: irreflexive and symmetric. -/
def K33 : SimpleGraph (Fin 3 ⊕ Fin 3) where
  Adj := K33Adj
  adj_symm := by
    intro a b h
    cases a <;> cases b
    · exact h
    · exact trivial
    · exact trivial
    · exact h
  adj_irrefl := by
    intro a
    cases a <;> simp [K33Adj]

/-- Unfolding lemma for the witness adjacency, left-to-right. -/
theorem K33_adj_il_ir (i j : Fin 3) : K33.Adj (Sum.inl i) (Sum.inr j) := trivial

/-- Unfolding lemma for the witness adjacency, right-to-left. -/
theorem K33_adj_ir_il (i j : Fin 3) : K33.Adj (Sum.inr i) (Sum.inl j) := trivial

/-- No adjacency within the left side. -/
theorem K33_not_adj_ll (i j : Fin 3) : ¬ K33.Adj (Sum.inl i) (Sum.inl j) := id

/-- No adjacency within the right side. -/
theorem K33_not_adj_rr (i j : Fin 3) : ¬ K33.Adj (Sum.inr i) (Sum.inr j) := id

/-- An edge of the witness has its endpoints on opposite sides. -/
theorem K33_adj_opposite {a b : Fin 3 ⊕ Fin 3} (h : K33.Adj a b) :
    (∃ i j, a = Sum.inl i ∧ b = Sum.inr j) ∨ (∃ i j, a = Sum.inr i ∧ b = Sum.inl j) := by
  cases a <;> cases b
  case inl.inl => exact absurd h (K33_not_adj_ll _ _)
  case inl.inr => exact Or.inl ⟨_, _, rfl, rfl⟩
  case inr.inl => exact Or.inr ⟨_, _, rfl, rfl⟩
  case inr.inr => exact absurd h (K33_not_adj_rr _ _)

/-- Adjacent vertices of the witness are distinct (faithfulness of the
simple-graph structure: no edge is a loop). -/
theorem K33_adj_ne {a b : Fin 3 ⊕ Fin 3} (h : K33.Adj a b) : a ≠ b := by
  intro e
  subst e
  exact K33.adj_irrefl _ h

/-- Symmetry of the witness adjacency, as a usable lemma. -/
theorem K33_symm {a b : Fin 3 ⊕ Fin 3} (h : K33.Adj a b) : K33.Adj b a :=
  K33.adj_symm a b h

end FlatBalance
