import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
namespace Literal
/-- A finite multigraph with numbered vertices. A connection is the whole entry. -/
structure Graph where
  order : Nat
  edge : Fin order → Fin order → Nat
  symm : ∀ i j, edge i j = edge j i
  loopless : ∀ i, edge i i = 0

def connection (g : Graph) (i j : Fin g.order) := g.edge i j
def doublyAdjacent (g : Graph) (i j : Fin g.order) : Prop := g.edge i j = 2
def degree (g : Graph) (i : Fin g.order) : Nat := ∑ j, g.edge i j
def SixRegular (g : Graph) : Prop := ∀ i, degree g i = 6
/-- Equivalent to doubling the adjacency matrix of a simple cubic graph. -/
def DoubledCubic (g : Graph) : Prop :=
  (∀ i j, g.edge i j = 0 ∨ g.edge i j = 2) ∧
  ∀ i, (Finset.univ.filter (fun j => g.edge i j = 2)).card = 3

/-- The target's labels can be any bijective numbering of the surviving vertices. -/
def YYDelta (g h : Graph) : Prop :=
  ∃ (x a b c : Fin g.order) (keep : Fin h.order → Fin g.order),
    g.order = h.order + 1 ∧ Function.Injective keep ∧
    (∀ v, v ≠ x ↔ ∃ i, keep i = v) ∧
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a ≠ x ∧ b ≠ x ∧ c ≠ x ∧
    (∀ v, g.edge x v = if v = a ∨ v = b ∨ v = c then 2 else 0) ∧
    (∀ i j, h.edge i j = g.edge (keep i) (keep j) +
      if i ≠ j ∧ (keep i = a ∨ keep i = b ∨ keep i = c) ∧
        (keep j = a ∨ keep j = b ∨ keep j = c) then 1 else 0)
/-- Inverse relation: remove one edge from each triangle pair and insert a double wye. -/
def DeltaYY (g h : Graph) : Prop := YYDelta h g
inductive Pure : Graph → Graph → Prop
| refl (g) : Pure g g
| step {g h k} : YYDelta g h → Pure h k → Pure g k

def PureResults (g : Graph) : Set Graph := {h | Pure g h}
def PureMinimum (g h : Graph) : Prop := Pure g h ∧ ∀ k, Pure g k → h.order ≤ k.order
inductive Equivalent : Graph → Graph → Prop
| refl (g) : Equivalent g g
| step {g h k} : (YYDelta g h ∨ DeltaYY g h) → Equivalent h k → Equivalent g k

def Minimal (g : Graph) : Prop := ∀ h, Equivalent g h → g.order ≤ h.order

/-- Undirected schematic edge; repetition represents distinct parallel edges. -/
abbrev Edge (n : Nat) := Fin n × Fin n

def pairCount {n} (es : List (Edge n)) (i j : Fin n) : Nat :=
  (es.filter (fun e => (e.1 = i ∧ e.2 = j) ∨ (e.1 = j ∧ e.2 = i))).length

def EndVertex (g : Graph) (i : Fin g.order) : Prop :=
  (Finset.univ.filter (fun j => 0 < g.edge i j)).card = 4 ∧ ∀ j, g.edge i j ≤ 2

/-- k+1 triangles on k+2 base vertices. Only bases must be distinct.
    Apex and attachment coincidences are checked by edge capacities. -/
structure Chain (g : Graph) (k : Nat) where
  base : Fin (k+2) → Fin g.order
  apex : Fin (k+1) → Fin g.order
  left : Fin 2 → Fin g.order
  right : Fin 2 → Fin g.order
  attach : Fin k → Fin g.order
  base_injective : Function.Injective base
  base_degree : ∀ i, degree g (base i) = 6
  left_end : EndVertex g (base 0)
  right_end : EndVertex g (base (Fin.last (k+1)))
  /-- The list reserves every actual schematic edge, including both copies of attachments. -/
  capacity : let es :=
    ((List.finRange (k+1)).flatMap fun t =>
      [(base t.castSucc, base t.succ), (base t.castSucc, apex t),
        (base t.succ, apex t)]) ++
    ((List.finRange 2).flatMap fun t =>
      [(base 0, left t), (base 0, left t),
       (base (Fin.last (k+1)), right t), (base (Fin.last (k+1)), right t)]) ++
    ((List.finRange k).flatMap fun t =>
      [(base t.succ.castSucc, attach t), (base t.succ.castSucc, attach t)])
    ∀ i j, pairCount es i j ≤ g.edge i j

def HasChain (g : Graph) : Prop := ∃ k, Nonempty (Chain g k)
def Conjecture51 : Prop := ∀ g, DoubledCubic g → ∀ h, PureMinimum g h →
  (Minimal h ↔ ¬ HasChain h)

theorem closed_certificate_sound (states : Set Graph) (b : Nat)
    (closed : ∀ g ∈ states, ∀ h, YYDelta g h → h ∈ states)
    (bound : ∀ g ∈ states, b ≤ g.order) {g h : Graph}
    (root : g ∈ states) (path : Pure g h) : b ≤ h.order := by
  have mem : h ∈ states := by
    induction path with
    | refl => exact root
    | @step g h k move rest ih => exact ih (closed g root h move)
  exact bound h mem

theorem smaller_equivalent_not_minimal {g h : Graph}
    (path : Equivalent g h) (drop : h.order < g.order) : ¬ Minimal g := by
  intro hm
  exact (Nat.not_le_of_lt drop) (hm h path)

/-- Exact conditional endpoint. No finite-certificate obligations are concealed. -/
theorem refutation_from_counterexample {g h small : Graph}
    (cubic : DoubledCubic g) (pure : Pure g h)
    (lower : ∀ k, Pure g k → h.order ≤ k.order)
    (noChain : ¬ HasChain h) (witness : Equivalent h small)
    (drop : small.order < h.order) : ¬ Conjecture51 := by
  intro hc
  have minimal := (hc g cubic h ⟨pure, lower⟩).mpr noChain
  exact smaller_equivalent_not_minimal witness drop minimal
#print axioms closed_certificate_sound
#print axioms refutation_from_counterexample
end Literal
