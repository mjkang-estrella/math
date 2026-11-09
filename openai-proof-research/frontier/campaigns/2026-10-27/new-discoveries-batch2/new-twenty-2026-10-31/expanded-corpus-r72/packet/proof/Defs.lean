import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Cover377831
open scoped BigOperators
abbrev Point (k : ℕ) := Fin k × Fin k × Fin k
abbrev Line (k : ℕ) := Fin 3 × Fin k × Fin k

def OnLine {k : ℕ} (p : Point k) (l : Line k) : Prop :=
  if l.1 = 0 then p.2.1 = l.2.1 ∧ p.2.2 = l.2.2
  else if l.1 = 1 then p.1 = l.2.1 ∧ p.2.2 = l.2.2
  else p.1 = l.2.1 ∧ p.2.1 = l.2.2
instance {k : ℕ} (p : Point k) (l : Line k) : Decidable (OnLine p l) := inferInstanceAs (Decidable (ite _ _ _))

def Covers {k : ℕ} (H : Finset (Point k)) (L : Finset (Line k)) : Prop :=
  ∀ p ∈ H, ∃ l ∈ L, OnLine p l

noncomputable def CoverNumber {k : ℕ} (H : Finset (Point k)) : ℕ :=
  sInf {n | ∃ L : Finset (Line k), L.card = n ∧ Covers H L}

-- A partial operation has at most one occurrence of each output in any row or column.
-- The block partition is represented by its surjective class map.
def ContainsSGQPQ {k : ℕ} (H : Finset (Point k)) (S : Finset (Fin k × Fin k)) : Prop :=
  ∃ n : ℕ, ∃ op : Fin n → Fin n → Option (Fin n), ∃ π : Fin n → Fin k,
    Function.Surjective π ∧
    (∀ a b c z, op a b = some z → op a c = some z → b = c) ∧
    (∀ a b c z, op a c = some z → op b c = some z → a = b) ∧
    (∀ a b, (π a, π b) ∈ S → ∃ z, op a b = some z) ∧
    (∀ a b z, op a b = some z → (π a, π b, π z) ∈ H)

def Restricted {k : ℕ} (H : Finset (Point k)) (S : Finset (Fin k × Fin k)) :=
  H.filter (fun p => (p.1, p.2.1) ∈ S)

def SourceConjecture : Prop := ∀ k (H : Finset (Point k)) (S : Finset (Fin k × Fin k)),
  CoverNumber (Restricted H S) = S.card → ContainsSGQPQ H S

def H : Finset (Point 3) :=
 { (0,0,2), (0,1,0), (0,1,1), (0,2,0), (0,2,1), (0,2,2),
   (1,0,0), (1,0,1), (1,1,1), (1,1,2), (1,2,0), (1,2,2),
   (2,0,0), (2,0,1), (2,1,2), (2,2,1), (2,2,2) }

def Y0 (i j : Fin 3) : ℤ :=
  if (i,j) = (0,2) ∨ (i,j) = (1,2) then 1
  else if (i,j) = (1,0) ∨ (i,j) = (2,0) then -1 else 0

def Y1 (i j : Fin 3) : ℤ :=
  if (i,j) = (0,0) then 1 else if (i,j) = (1,2) then -1 else 0

def Y2 (i j : Fin 3) : ℤ :=
  if (i,j) = (1,2) then 1 else if (i,j) = (0,0) ∨ (i,j) = (2,1) then -1 else 0

def T (i j : Fin 3) : ℤ := Y0 i j + Y1 i j + Y2 i j

theorem score_zero : ∀ p ∈ H, Y0 p.2.1 p.2.2 + Y1 p.1 p.2.2 + Y2 p.1 p.2.1 = 0 := by decide

theorem symmetric_score : ∀ i j : Fin 3,
    T i j + T j i = if (i,j) = (0,1) ∨ (i,j) = (1,0) then -1 else 0 := by decide
end Cover377831
