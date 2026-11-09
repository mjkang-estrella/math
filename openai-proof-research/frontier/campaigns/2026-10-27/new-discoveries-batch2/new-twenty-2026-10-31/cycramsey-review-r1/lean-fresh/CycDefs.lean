import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-!
# Cyclic Ramsey numbers (arXiv:2604.16188, Sections 1-2)

Graphs have vertex set `{0, …, k-1}` (`Fin k`).  A `2`-edge-colouring of `K_n` is a map
`Sym2 (Fin n) → Fin 2`; colour `0` is the paper's colour `1` and colour `1` is colour `2`.
An embedding `φ : V(H) → V(K_n)` is *cyclic* if it is injective and there is `t ∈ V(H)` such that
`(φ(t), φ(t+1), …, φ(k-1), φ(0), …, φ(t-1))` is increasing, i.e. `j ↦ φ (t + j)` is strictly
monotone (addition in `Fin k`).
-/

namespace CycRamsey

theorem ite_t {α : Sort*} {p : Prop} [Decidable p] (h : p) (x y : α) :
    (if p then x else y) = x := by simp [h]

theorem ite_f {α : Sort*} {p : Prop} [Decidable p] (h : ¬ p) (x y : α) :
    (if p then x else y) = y := by simp [h]

/-- A 2-edge-colouring of the complete graph on `Fin n`. -/
abbrev Colouring (n : ℕ) := Sym2 (Fin n) → Fin 2

/-- `φ` is increasing up to a cyclic permutation (and injective). -/
def IsCyclicEmbedding {k n : ℕ} (φ : Fin k → Fin n) : Prop :=
  Function.Injective φ ∧ ∃ t : Fin k, StrictMono (fun j : Fin k => φ (t + j))

/-- `c` contains `H` as a monochromatic subgraph of colour `i`, vertices in the same cyclic order. -/
def ContainsCyc {k n : ℕ} (H : SimpleGraph (Fin k)) (c : Colouring n) (i : Fin 2) : Prop :=
  ∃ φ : Fin k → Fin n, IsCyclicEmbedding φ ∧ ∀ u v, H.Adj u v → c s(φ u, φ v) = i

/-- Every 2-edge-colouring of `K_n` contains `H₁` in colour 1 or `H₂` in colour 2 (cyclically). -/
def CycRamseyProp {k₁ k₂ : ℕ} (H₁ : SimpleGraph (Fin k₁)) (H₂ : SimpleGraph (Fin k₂)) (n : ℕ) :
    Prop :=
  ∀ c : Colouring n, ContainsCyc H₁ c 0 ∨ ContainsCyc H₂ c 1

/-- The cyclic Ramsey number `R_cyc(H₁, H₂)`: the smallest such `n`. -/
noncomputable def cycRamsey {k₁ k₂ : ℕ} (H₁ : SimpleGraph (Fin k₁)) (H₂ : SimpleGraph (Fin k₂)) :
    ℕ :=
  sInf {n | CycRamseyProp H₁ H₂ n}

/-- The start-central star `S_a^{sc}` of order `a`: vertex `0` is adjacent to all other vertices. -/
def startStar (a : ℕ) : SimpleGraph (Fin a) :=
  SimpleGraph.fromRel (fun u v => u.val = 0 ∧ v.val ≠ 0)

/-- The monotone path `P_b^{mon}` of order `b`: vertices adjacent iff consecutive integers. -/
def monPath (b : ℕ) : SimpleGraph (Fin b) :=
  SimpleGraph.fromRel (fun u v => u.val + 1 = v.val)

end CycRamsey
