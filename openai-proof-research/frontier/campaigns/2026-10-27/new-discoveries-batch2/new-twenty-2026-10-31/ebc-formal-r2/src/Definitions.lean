import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open SimpleGraph Finset
namespace EBC337062
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Literal shortest paths, represented by path-filtered walks of minimum length. -/
noncomputable def shortestPaths (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V) : Finset (G.Walk x y) := by
  classical
  exact (G.finsetWalkLength (G.dist x y) x y).filter (fun w => w.IsPath)

/-- The path condition is redundant at the minimum length. -/
theorem shortestPaths_eq (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    shortestPaths G x y = G.finsetWalkLength (G.dist x y) x y := by
  classical
  apply Finset.filter_eq_self.mpr
  intro w hw
  exact w.isPath_of_length_eq_dist ((G.mem_finsetWalkLength_iff).mp hw)

noncomputable def sigma (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) : ℕ :=
  (shortestPaths G x y).card

noncomputable def sigmaEdge (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V) (e : Sym2 V) : ℕ := by
  classical
  exact ((shortestPaths G x y).filter (fun w => e ∈ w.edges)).card

theorem sigma_eq_walk_count (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    sigma G x y = (G.finsetWalkLength (G.dist x y) x y).card := by
  rw [sigma, shortestPaths_eq]

noncomputable def edgeBetweenness (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Sym2 V) : ℚ :=
  ∑ x : V, ∑ y ∈ (univ.filter (fun y => y ≠ x)),
    (sigmaEdge G x y e : ℚ) / (sigma G x y : ℚ)

noncomputable def EdgeBetweennessUniform (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ e ∈ G.edgeSet, ∀ e' ∈ G.edgeSet, edgeBetweenness G e = edgeBetweenness G e'

def EdgeTransitive (G : SimpleGraph V) : Prop :=
  ∀ e ∈ G.edgeSet, ∀ e' ∈ G.edgeSet, ∃ φ : G ≃g G, Sym2.map φ e = e'

/-- Arbitrary-order circulant with an arbitrary jump set; loops are removed. -/
def circulant (m : ℕ) (s : Set (ZMod m)) : SimpleGraph (ZMod m) :=
  SimpleGraph.circulantGraph s

theorem circulant_adj (m : ℕ) (s : Set (ZMod m)) (x y : ZMod m) :
    (circulant m s).Adj x y ↔ x ≠ y ∧ (x-y ∈ s ∨ y-x ∈ s) := Iff.rfl

def circ (m a b c : ℕ) : SimpleGraph (ZMod m) :=
  circulant m {(a : ZMod m), (b : ZMod m), (c : ZMod m)}

instance circDecidable (m a b c : ℕ) : DecidableRel (circ m a b c).Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.circulantGraph
    ({(a : ZMod m), (b : ZMod m), (c : ZMod m)} : Set (ZMod m))).Adj)

/-- Class index 0 means source Class 3, through index 6 meaning Class 9.
The order is expressed as a successor to supply finite-vertex instances literally. -/
def classData (c : Fin 7) (n : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  match c.val with
  | 0 => (19 + 8 * (n-1) + 1, 1, 2*n+2, 2*n+4)
  | 1 => (31 + 8 * (n-1) + 1, 1, 2*n+5, 2*n+7)
  | 2 => (19 + 16 * (n-1) + 1, 1, 4*n, 8*n+1)
  | 3 => (27 + 16 * (n-1) + 1, 1, 4*n+4, 8*n+5)
  | 4 => (31 + 8 * (n-1) + 1, 1, 2*n+5, 4*n+11)
  | 5 => (31 + 8 * (n-1) + 1, 1, 2*n+7, 4*n+11)
  | _ => (48 + 14 * (n-1) + 1, 1, 2*n+6, 4*n+9)

theorem classData_pos (c : Fin 7) (n : ℕ) : 0 < (classData c n).1 := by
  fin_cases c <;> simp [classData]

noncomputable def classProperty (c : Fin 7) (n : ℕ) : Prop :=
  let d := classData c n
  letI : NeZero d.1 := ⟨Nat.ne_of_gt (classData_pos c n)⟩
  EdgeBetweennessUniform (circ d.1 d.2.1 d.2.2.1 d.2.2.2) ∧
    ¬ EdgeTransitive (circ d.1 d.2.1 d.2.2.1 d.2.2.2)

noncomputable def Conjecture21 : Prop := ∀ c : Fin 7, ∀ n : ℕ, 1 ≤ n → classProperty c n

abbrev G32 := circ 32 1 7 9

theorem class4_n1 : classData 1 1 = (32,1,7,9) := rfl
end EBC337062
