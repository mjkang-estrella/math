module
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Sym

/-! Source model for MathDB 338806. No existence or expansion assumptions.
Scientific HOLD; this model alone does not refute the conjecture. -/
@[expose] public section
namespace URMatching
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A finite set of actual unordered graph edges, pairwise vertex-disjoint. -/
def IsMatching (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧
  ∀ e ∈ M, ∀ f ∈ M, ∀ v : V, v ∈ e → v ∈ f → e = f

/-- Vertices covered by the matching, without any induced-subgraph restriction. -/
def Covered (M : Finset (Sym2 V)) : Set V := {v | ∃ e ∈ M, v ∈ e}

/-- Literal uniqueness among ALL matchings covering exactly the same vertices. -/
def IsUR (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  IsMatching G M ∧ ∀ M' : Finset (Sym2 V),
    IsMatching G M' → Covered M' = Covered M → M' = M

noncomputable def matchingNumber (G : SimpleGraph V) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Finset (Sym2 V))).filter (IsMatching G)).sup Finset.card

noncomputable def urMatchingNumber (G : SimpleGraph V) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Finset (Sym2 V))).filter (IsUR G)).sup Finset.card

/-- All vertices satisfy the genuine finite neighbor-cardinality bound. -/
def DegreeBound (G : SimpleGraph V) (Δ : ℕ) : Prop :=
  ∀ v, by classical exact ((Finset.univ : Finset V).filter (G.Adj v)).card ≤ Δ

end URMatching
