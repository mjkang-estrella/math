import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Find

namespace IntervalWidth

/-- Input order is the index order. Endpoint separation is weak, as in the source. -/
structure Interval (α : Type*) where
  left : α
  right : α

def Compatible {α : Type*} [LE α] {n : Nat}
    (I : Fin n → Interval α) (i j : Fin n) : Prop :=
  i < j ∧ (I i).right ≤ (I j).left

/-- A path follows parent pointers from an ancestor to a descendant. -/
inductive Path {n : Nat} (parent : Fin n → Option (Fin n)) : Fin n → Fin n → Prop
  | refl (i) : Path parent i i
  | step {r i j} : Path parent r i → parent j = some i → Path parent r j

/-- A partition into exactly r nonempty rooted chronological k-ary trees.
The explicit root paths ensure that one class cannot contain several trees. -/
structure HeapPartition {α : Type*} [LE α] {n : Nat}
    (k : Nat) (I : Fin n → Interval α) (r : Nat) where
  color : Fin n → Fin r
  root : Fin r → Fin n
  root_color : ∀ a, color (root a) = a
  parent : Fin n → Option (Fin n)
  root_parent : ∀ a, parent (root a) = none
  parent_color : ∀ i j, parent j = some i → color i = color j
  edge : ∀ i j, parent j = some i → Compatible I i j
  arity : ∀ i, (Finset.univ.filter (fun j => parent j = some i)).card ≤ k
  rooted : ∀ j, Path parent (root (color j)) j

/-- The singleton partition witnesses existence even when k=0 or n=0. -/
def singletonPartition {α : Type*} [LE α] {n : Nat}
    (k : Nat) (I : Fin n → Interval α) : HeapPartition k I n where
  color := id
  root := id
  root_color := fun _ => rfl
  parent := fun _ => none
  root_parent := fun _ => rfl
  parent_color := by intros i j h; cases h
  edge := by intros i j h; cases h
  arity := by intro i; simp
  rooted := fun j => Path.refl j

theorem partition_exists {α : Type*} [LE α] {n : Nat}
    (k : Nat) (I : Fin n → Interval α) : ∃ r, Nonempty (HeapPartition k I r) :=
  ⟨n, ⟨singletonPartition k I⟩⟩

/-- Source k-width: the attained minimum number of heapable partition classes. -/
noncomputable def width {α : Type*} [LE α] {n : Nat}
    (k : Nat) (I : Fin n → Interval α) : Nat := by
  classical
  exact Nat.find (partition_exists k I)

end IntervalWidth
