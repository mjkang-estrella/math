import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.ENat.Basic
namespace Toroidal
abbrev Vertex (m n : Nat) := Fin m × Fin n
def CycleAdj (m a b : Nat) : Prop := (a + 1) % m = b ∨ (b + 1) % m = a
def Adj (m n : Nat) (x y : Vertex m n) : Prop :=
 (x.1 = y.1 ∧ CycleAdj n x.2.val y.2.val) ∨
 (x.2 = y.2 ∧ CycleAdj m x.1.val y.1.val)
instance (m n : Nat) (x y : Vertex m n) : Decidable (Adj m n x y) :=
 by unfold Adj CycleAdj; infer_instance
def Alternates {α : Type} [DecidableEq α] (w : List α) (x y : α) : Prop :=
 ((w.filter (fun z => z = x ∨ z = y)).zip
  ((w.filter (fun z => z = x ∨ z = y)).drop 1)).all (fun p => p.1 != p.2) = true
def Represents (m n k : Nat) (w : List (Vertex m n)) : Prop :=
 (∀ x : Vertex m n, w.count x = k) ∧
 (∀ x y : Vertex m n, x ≠ y → (Alternates w x y ↔ Adj m n x y))
def HasRepresentation (m n k : Nat) : Prop := ∃ w, Represents m n k w
noncomputable def representationNumber (m n : Nat) : WithTop Nat := by
 classical
 exact
 if h : ∃ k, 0 < k ∧ HasRepresentation m n k then (Nat.find h : WithTop Nat) else ⊤
def Conjecture1 : Prop :=
 ∀ m n : Nat, 3 ≤ m → 3 ≤ n → 8 ≤ m + n → 4 ≤ representationNumber m n
end Toroidal
