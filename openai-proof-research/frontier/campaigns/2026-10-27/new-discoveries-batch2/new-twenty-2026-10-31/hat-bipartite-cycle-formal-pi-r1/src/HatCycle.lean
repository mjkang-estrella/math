import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-!
# Hat graph `K^hat(s)`: faithful source model and first kernel lemma

Literal label model of the source graph (Heinig Definition 3, MathDB 325100):
vertices are the labels `0, 1, ..., 2s-1`, realized as `Fin (2*s)`.  The odd
labels `1, 3, ..., 2s-1` form `A` (so `a = 1`, `b = 2s-1`), the positive even
labels `2, 4, ..., 2s-2` form `B`.  Every `A`-`B` pair is an undirected edge;
in addition the vertex `0` is adjacent to exactly `1` and `2s-1`.  No loops,
no other edges.  Edges are carried by the actual finite edge set `hatEdgeSet`,
stored once in canonical increasing-label orientation.

F2 edge vectors are functions `HEdge s -> ZMod 2` on that literal edge set;
`Bnd` is the boundary (parity-of-incidence) map.  A Hamilton circuit is a
spanning connected 2-regular subgraph given by an explicit set of source
edges (`HamCirc`), not by any kernel-membership condition.

First proved bridge: the edge vector of any Hamilton circuit has even
incidence at every vertex, and consequently the span of the Hamilton circuit
vectors is contained in the even-incidence kernel.
-/

/-- Canonical undirected edge set of the hat graph `K^hat(s)`: pairs of
distinct labels in increasing order; `A`-`B` pairs (both nonzero, opposite
parity) plus the two `z`-edges `{0,1}` and `{0,2s-1}`. -/
def hatEdgeSet (s : Nat) : Finset (Fin (2 * s) × Fin (2 * s)) :=
  Finset.univ.filter fun e =>
    e.1.val < e.2.val ∧
      ((e.1.val ≠ 0 ∧ e.2.val ≠ 0 ∧ (e.1.val + e.2.val) % 2 = 1) ∨
        (e.1.val = 0 ∧ (e.2.val = 1 ∨ e.2.val = 2 * s - 1)))

/-- The hat-graph edges, as a type. -/
abbrev HEdge (s : Nat) := {e : Fin (2 * s) × Fin (2 * s) // e ∈ hatEdgeSet s}

/-- Undirected adjacency of the source graph: distinct vertices joined by an
actual hat edge (in either orientation). -/
def hatAdj (s : Nat) (u v : Fin (2 * s)) : Prop :=
  u ≠ v ∧ ∃ e : HEdge s, e.1 = (u, v) ∨ e.1 = (v, u)

theorem hatAdj_symm (s : Nat) (u v : Fin (2 * s)) (h : hatAdj s u v) : hatAdj s v u := by
  unfold hatAdj at h ⊢
  refine ⟨fun hba => h.1 hba.symm, ?_⟩
  cases h.2 with
  | intro e he =>
    refine ⟨e, ?_⟩
    cases he with
    | inl h9 => exact Or.inr h9
    | inr h9 => exact Or.inl h9

theorem hatAdj_irrefl (s : Nat) (v : Fin (2 * s)) : ¬ hatAdj s v v := by
  intro h
  unfold hatAdj at h
  exact h.1 rfl

/-- Incidence of the edge `e` at the vertex `v` (literal endpoint test). -/
abbrev IncidP (s : Nat) (v : Fin (2 * s)) (e : HEdge s) : Prop := e.1.1 = v ∨ e.1.2 = v

/-- Boundary (parity of incident edge coefficients) at vertex `v`. -/
def Bnd (s : Nat) (f : HEdge s → ZMod 2) (v : Fin (2 * s)) : ZMod 2 :=
  Finset.sum (Finset.univ.filter (IncidP s v)) fun e => f e

/-- Walk-connectedness of a set of hat edges. -/
inductive Rch (s : Nat) (F : Finset (HEdge s)) : Fin (2 * s) → Fin (2 * s) → Prop
  | refl (v : Fin (2 * s)) : Rch s F v v
  | step (u v w : Fin (2 * s)) (h : ∃ e ∈ F, e.1 = (u, v) ∨ e.1 = (v, u)) :
      Rch s F v w → Rch s F u w

/-- A Hamilton circuit of the source graph: a set of genuine hat edges in
which every vertex of `Fin (2*s)` lies on exactly two edges, and which is
connected.  Spanning and 2-regular are the deg2 field; connectedness is
`conn`. -/
structure HamCirc (s : Nat) where
  edges : Finset (HEdge s)
  deg2 : ∀ v : Fin (2 * s), Finset.card (Finset.filter (IncidP s v) edges) = 2
  conn : ∀ u v : Fin (2 * s), Rch s edges u v

/-- The F2 edge vector of a Hamilton circuit: indicator of its edge set. -/
def HamVec (s : Nat) (c : HamCirc s) : HEdge s → ZMod 2 :=
  fun e => if e ∈ c.edges then (1 : ZMod 2) else (0 : ZMod 2)

/-- Summing an indicator over any finite index set counts the elements that
lie in `F`. -/
theorem sum_indicator_card {α : Type} [DecidableEq α] (F : Finset α) :
    ∀ U : Finset α,
      Finset.sum U (fun x => if x ∈ F then (1 : ZMod 2) else (0 : ZMod 2))
        = ((Finset.filter (fun x => x ∈ F) U).card : ZMod 2) := by
  intro U
  induction U using Finset.induction with
  | empty => simp
  | insert a U' hnin ih =>
    have hUf : ¬ (a ∈ Finset.filter (fun x => x ∈ F) U') := by
      intro hh
      rw [Finset.mem_filter] at hh
      exact hnin hh.1
    rw [Finset.sum_insert hnin, ih, Finset.filter_insert]
    by_cases hF : a ∈ F
    · simp only [hF, ite_true]
      rw [Finset.card_insert_of_notMem hUf, Nat.cast_add, Nat.cast_one, add_comm]
    · simp only [hF, ite_false, zero_add]

/-- The edge vector of a Hamilton circuit has even incidence at every vertex:
genuine circuits lie in the boundary kernel. -/
theorem hamVec_even (s : Nat) (c : HamCirc s) (v : Fin (2 * s)) :
    Bnd s (HamVec s c) v = 0 := by
  have h1 : Bnd s (HamVec s c) v
      = (((Finset.univ.filter (IncidP s v)).filter fun e => e ∈ c.edges).card : ZMod 2) :=
    sum_indicator_card c.edges (Finset.univ.filter (IncidP s v))
  have hAB : ((Finset.univ.filter (IncidP s v)).filter fun e => e ∈ c.edges)
      = Finset.filter (IncidP s v) c.edges := by
    refine Finset.ext fun e => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [h1, hAB, c.deg2 v]
  exact ZMod.natCast_self 2

/-- The even-incidence kernel as a submodule of the F2 edge space. -/
def CycleKernel (s : Nat) : Submodule (ZMod 2) (HEdge s → ZMod 2) where
  carrier := {f | ∀ v : Fin (2 * s), Bnd s f v = 0}
  zero_mem' := by
    intro v
    simp [Bnd]
  add_mem' := by
    intro f g hf hg v
    have h : Bnd s (f + g) v = Bnd s f v + Bnd s g v := by
      simp only [Bnd, Pi.add_apply, Finset.sum_add_distrib]
    rw [h, hf v, hg v, add_zero]
  smul_mem' := by
    intro a f hf v
    have h : Bnd s (a • f) v = a • Bnd s f v := by
      simp only [Bnd, Pi.smul_apply, Finset.smul_sum]
    rw [h, hf v, smul_zero]

/-- The F2 span of the Hamilton circuit edge vectors. -/
def HamSpan (s : Nat) : Submodule (ZMod 2) (HEdge s → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range fun c : HamCirc s => HamVec s c)

/-- The span of the Hamilton circuit vectors is contained in the even
incidence kernel: the "converse" half of the cycle-space theorem. -/
theorem hamSpan_le (s : Nat) : HamSpan s ≤ CycleKernel s := by
  refine Submodule.span_le.2 ?_
  intro x hx
  obtain ⟨c, rfl⟩ := hx
  intro v
  exact hamVec_even s c v
