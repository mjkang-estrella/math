import AntimagicBasics
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.Sigma

namespace Antimagic
abbrev Vertex (t n : ℕ) := (h : Fin (n + 1)) × Fin (t ^ h.val)

def depth {t n : ℕ} (v : Vertex t n) : ℕ := v.1.val

def Child {t n : ℕ} (u v : Vertex t n) : Prop :=
  v.1.val = u.1.val + 1 ∧ v.2.val / t = u.2.val

instance {t n : ℕ} : DecidableRel (@Child t n) := fun _ _ => inferInstanceAs (Decidable (_ = _ ∧ _ = _))

def tree (t n : ℕ) : SimpleGraph (Vertex t n) where
  Adj u v := Child u v ∨ Child v u
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨by intro v h; rcases h with h | h <;> have := h.1 <;> omega⟩

instance (t n : ℕ) : DecidableRel (tree t n).Adj := fun _ _ =>
  inferInstanceAs (Decidable (Child _ _ ∨ Child _ _))

def root (t n : ℕ) : Vertex t n := ⟨⟨0, by omega⟩, ⟨0, by simp⟩⟩

theorem root_depth (t n : ℕ) : depth (root t n) = 0 := rfl

theorem unique_depth_zero {t n : ℕ} (v : Vertex t n) (h : depth v = 0) :
    v = root t n := by
  obtain ⟨⟨h, hh⟩, ⟨i, hi⟩⟩ := v
  simp only [depth] at h
  subst h
  simp only [pow_zero] at hi
  have : i = 0 := by omega
  subst i
  rfl

/-- Structural source predicate. Depth rises by one on children; every nonroot
has exactly one parent; a nonleaf has exactly t children; terminal depth is n. -/
structure FullTree {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (t n : ℕ) where
  root : V
  depth : V → ℕ
  child : V → V → Prop
  childDec : DecidableRel child
  isTree : G.IsTree
  root_zero : ∀ v, depth v = 0 ↔ v = root
  adj_iff : ∀ u v, G.Adj u v ↔ child u v ∨ child v u
  child_depth : ∀ u v, child u v → depth v = depth u + 1
  unique_parent : ∀ v, v ≠ root → ∃! u, child u v
  depth_le : ∀ v, depth v ≤ n
  child_count : ∀ v, (letI := childDec v; (Finset.univ.filter (child v)).card) =
    if depth v < n then t else 0

/-- Remaining structural verification, not a supplied proof. -/
def ModelStructure : Prop := ∀ t n, 2 ≤ t → 1 ≤ n →
  ∃ S : FullTree (tree t n) t n, S.root = root t n ∧ S.depth = depth ∧ S.child = Child

/-- Remaining uniqueness bridge for arbitrary source trees. -/
def ModelBridge : Prop := ∀ (V : Type) [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (t n : ℕ),
  2 ≤ t → 1 ≤ n → FullTree G t n → Nonempty (G ≃g tree t n)

/-- Degree-one leaves, including the source's convention at the root. -/
def ModelLeaves : Prop := ∀ t n, 2 ≤ t → 1 ≤ n → numLeaves (tree t n) = t ^ n
end Antimagic
