/-
  MathDB 346320 — Kobeaga–Merino–Lozano, arXiv:2004.14574v4, Conjecture 6.2, SRK = S1S2.

  *** UNCOMPILED DRAFT ***  (Claude lane: Lean/lake were NOT run, by lane restriction.)
  Root / a Sol worker must compile it with the pinned toolchain
  (Lean 4.34.1, mathlib d13f23b723b8a846827a245b89c10fc7d3f11612), strict, and audit axioms.

  Model.  A state of the shrinking process on the vertex set `Fin n` of the input graph is a
  labelling `L : Fin n → Fin n`; the current (shrunk) vertices are the blocks
  `{u | L u = L a}`, represented by the labels `a` with `L a = a`.  Shrinking two current
  vertices merges their blocks (source eq. (15)); the edge value between two current vertices is
  the sum of the original edge values between the blocks (16a,16b); the value of an unmerged vertex
  is its original `y` (16c) and that of a merged vertex is half its boundary value (16d).
  `Move` is exactly the set of pairs on which Algorithm S1S2 (Appendix A.1) performs a shrink:
  rule S1 (Theorem 4.4): x[u,v] = y_u = y_v = c and some other vertex w has y_w ≥ c;
  rule S2 (Theorem 4.5): x[u,v] > max{y_u, y_v}.  Only adjacent pairs (positive edge value) are
  considered, as the algorithm scans `v ∈ N(u)` in the support graph.
-/
import Mathlib

namespace MathDB346320

open Finset

variable {n : ℕ}

/-- Membership of `(y, x)` in the assignment polytope `P_A^{K_n}` (source (7a),(7b),(7e),(7f)),
with `x` a symmetric loopless edge-value matrix. -/
def InPA (y : Fin n → ℚ) (x : Fin n → Fin n → ℚ) : Prop :=
  (∀ u v, x u v = x v u) ∧ (∀ u, x u u = 0) ∧
  (∀ v, ∑ u, x v u = 2 * y v) ∧                      -- (7a) degree equations
  (∀ u v, x u v ≤ y u) ∧                             -- (7b) logical constraints
  (∀ v, 0 ≤ y v ∧ y v ≤ 1) ∧ (∀ u v, 0 ≤ x u v)       -- (7e),(7f)

abbrev Lab (n : ℕ) := Fin n → Fin n

/-- The block (current vertex) containing `a`. -/
def blk (L : Lab n) (a : Fin n) : Finset (Fin n) := univ.filter (fun u => L u = L a)

/-- Edge value between the current vertices containing `a` and `b` (16a),(16b). -/
def X (x : Fin n → Fin n → ℚ) (L : Lab n) (a b : Fin n) : ℚ :=
  ∑ u ∈ blk L a, ∑ w ∈ blk L b, x u w

/-- Vertex value of the current vertex containing `a`: original value if unmerged (16c),
half the boundary value if merged (16d). -/
def Y (y : Fin n → ℚ) (x : Fin n → Fin n → ℚ) (L : Lab n) (a : Fin n) : ℚ :=
  if blk L a = {a} then y a
  else (∑ u ∈ blk L a, ∑ w ∈ univ.filter (fun w => L w ≠ L a), x u w) / 2

/-- A shrink performed by Algorithm S1S2 on the current vertices containing `a`, `b`. -/
def Move (y : Fin n → ℚ) (x : Fin n → Fin n → ℚ) (L : Lab n) (a b : Fin n) : Prop :=
  L a ≠ L b ∧ 0 < X x L a b ∧
  ((Y y x L a = Y y x L b ∧ X x L a b = Y y x L a ∧
      ∃ w, L w ≠ L a ∧ L w ≠ L b ∧ Y y x L a ≤ Y y x L w) ∨
    (Y y x L a < X x L a b ∧ Y y x L b < X x L a b))

instance (y : Fin n → ℚ) (x : Fin n → Fin n → ℚ) (L : Lab n) (a b : Fin n) :
    Decidable (Move y x L a b) := by unfold Move; infer_instance

/-- Shrinking: relabel the block of `b` by the label of `a`. -/
def merge (L : Lab n) (a b : Fin n) : Lab n := fun u => if L u = L b then L a else L u

def Step (y : Fin n → ℚ) (x : Fin n → Fin n → ℚ) (L L' : Lab n) : Prop :=
  ∃ a b, Move y x L a b ∧ L' = merge L a b

/-- No rule of the strategy applies any more (the heap empties without a shrink). -/
def Terminal (y : Fin n → ℚ) (x : Fin n → Fin n → ℚ) (L : Lab n) : Prop :=
  ¬ ∃ L', Step y x L L'

/-- A final shrunk state obtained by applying the strategy S1S2 exhaustively to `(y, x)`. -/
def Obtained (y : Fin n → ℚ) (x : Fin n → Fin n → ℚ) (L : Lab n) : Prop :=
  Relation.ReflTransGen (Step y x) id L ∧ Terminal y x L

/-- Current vertices: labels that represent their block. -/
abbrev Rep (L : Lab n) := {a : Fin n // L a = a}

/-- The shrunk support graph: current vertices, adjacent iff positive edge value. -/
def shrunk (x : Fin n → Fin n → ℚ) (L : Lab n) : SimpleGraph (Rep L) where
  Adj a b := a ≠ b ∧ (0 < X x L a.1 b.1 ∨ 0 < X x L b.1 a.1)
  symm := fun a b h => ⟨h.1.symm, h.2.symm⟩
  loopless := fun a h => h.1 rfl

/-! ## The six-vertex instance -/

/-- `y = (1/2, 1, 1, 1, 1, 1)`. -/
def y0 : Fin 6 → ℚ := ![1/2, 1, 1, 1, 1, 1]

/-- Support edges: {0,4},{0,5},{2,3},{2,5},{3,4} with value 1/2 and {1,2},{1,3},{4,5} with value 1. -/
def x0 : Fin 6 → Fin 6 → ℚ :=
  ![![0,   0, 0,   0,   1/2, 1/2],
    ![0,   0, 1,   1,   0,   0  ],
    ![0,   1, 0,   1/2, 0,   1/2],
    ![0,   1, 1/2, 0,   1/2, 0  ],
    ![1/2, 0, 0,   1/2, 0,   1  ],
    ![1/2, 0, 1/2, 0,   1,   0  ]]

theorem inPA : InPA y0 x0 := by
  unfold InPA y0 x0; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Terminal labellings: run A ends with blocks {0}, {4,5}, {1,2,3}; run B with
{0}, {4}, {5}, {1,2,3}. -/
def LA : Lab 6 := ![0, 1, 1, 1, 4, 4]
def LB : Lab 6 := ![0, 1, 1, 1, 4, 5]

/- Run A: S1 on {4,5} (witness 1), S1 on {1,2} (witness 3), S2 on {{1,2},3} (x = 3/2 > 1). -/
def A1 : Lab 6 := merge id 4 5
def A2 : Lab 6 := merge A1 1 2
/- Run B: S1 on {1,2} (witness 3), S2 on {{1,2},3}. -/
def B1 : Lab 6 := merge id 1 2

theorem stepA1 : Step y0 x0 id A1 := ⟨4, 5, by decide, rfl⟩
theorem stepA2 : Step y0 x0 A1 A2 := ⟨1, 2, by decide, rfl⟩
theorem stepA3 : Step y0 x0 A2 LA := ⟨1, 3, by decide, by funext u; fin_cases u <;> decide⟩
theorem stepB1 : Step y0 x0 id B1 := ⟨1, 2, by decide, rfl⟩
theorem stepB2 : Step y0 x0 B1 LB := ⟨1, 3, by decide, by funext u; fin_cases u <;> decide⟩

theorem terminal_iff (y : Fin n → ℚ) (x : Fin n → Fin n → ℚ) (L : Lab n) :
    Terminal y x L ↔ ∀ a b, ¬ Move y x L a b := by
  unfold Terminal Step
  constructor
  · intro h a b hm; exact h ⟨merge L a b, a, b, hm, rfl⟩
  · rintro h ⟨L', a, b, hm, -⟩; exact h a b hm

theorem termA : Terminal y0 x0 LA := (terminal_iff _ _ _).2 (by decide)
theorem termB : Terminal y0 x0 LB := (terminal_iff _ _ _).2 (by decide)

theorem obtainedA : Obtained y0 x0 LA :=
  ⟨Relation.ReflTransGen.tail (Relation.ReflTransGen.tail
      (Relation.ReflTransGen.single stepA1) stepA2) stepA3, termA⟩

theorem obtainedB : Obtained y0 x0 LB :=
  ⟨Relation.ReflTransGen.tail (Relation.ReflTransGen.single stepB1) stepB2, termB⟩

theorem cardA : Fintype.card (Rep LA) = 3 := by decide
theorem cardB : Fintype.card (Rep LB) = 4 := by decide

/-- **Main theorem (negation of Conjecture 6.2 for SRK = S1S2).**  There is a vector `(y, x)`
in the assignment polytope of `K_6` such that two final graphs obtained by applying the
shrinking strategy S1S2 to `(y, x)` are not isomorphic (they have 3 and 4 vertices). -/
theorem conjecture_6_2_false :
    ∃ (n : ℕ) (y : Fin n → ℚ) (x : Fin n → Fin n → ℚ), InPA y x ∧
      ¬ ∀ L₁ L₂ : Lab n, Obtained y x L₁ → Obtained y x L₂ →
          Nonempty (shrunk x L₁ ≃g shrunk x L₂) := by
  refine ⟨6, y0, x0, inPA, fun h => ?_⟩
  obtain ⟨e⟩ := h LA LB obtainedA obtainedB
  have := Fintype.card_congr e.toEquiv
  rw [cardA, cardB] at this
  omega

end MathDB346320
