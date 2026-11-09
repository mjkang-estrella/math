import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Relation
import Lean.Elab.Tactic.Omega

namespace Chord
/-- Endpoints in their literal cyclic backbone order; chord names are suppressed. -/
structure Diagram (n : Nat) where
  partner : Fin (2*n) → Fin (2*n)
  involutive : ∀ i, partner (partner i) = i
  noFixed : ∀ i, partner i ≠ i

abbrev Sides (n : Nat) := Fin (2*n) → Bool

/-- Raw endpoint arithmetic is total; values outside the endpoint set are never traced. -/
def mate {n} (D : Diagram n) (i : Nat) : Nat :=
  if h : i < 2*n then (D.partner ⟨i,h⟩).val else i

def side {n} (c : Sides n) (i : Nat) : Bool :=
  if h : i < 2*n then c ⟨i,h⟩ else false

/-- P=0, N=1, C=2 at every vertex. -/
def theta {n} (D : Diagram n) (h : Nat) : Nat :=
  let i := h / 3
  match h % 3 with
  | 0 => 3*((i+2*n-1) % (2*n))+1
  | 1 => 3*((i+1) % (2*n))
  | _ => 3*mate D i+2

/-- Inner rotation N→C→P→N; outer rotation N→P→C→N. -/
def rho {n} (c : Sides n) (h : Nat) : Nat :=
  3*(h/3) + if side c (h/3) then
    (match h%3 with | 0 => 2 | 1 => 0 | _ => 1)
  else (match h%3 with | 0 => 1 | 1 => 2 | _ => 0)

def face {n} (D : Diagram n) (c : Sides n) (h : Nat) : Nat := rho c (theta D h)

/-- Fuel-bounded orbit traversal, with a visited list shared across starting points. -/
def trace (f : Nat → Nat) (fuel i : Nat) (seen : List Nat) : List Nat :=
  Nat.rec (fun _ s => s)
    (fun _ ih j s => if j ∈ s then s else ih (f j) (j::s)) fuel i seen

def cycles (size : Nat) (f : Nat → Nat) : Nat :=
  ((List.range size).foldl (fun (s : Nat × List Nat) i =>
    if i ∈ s.2 then s else (s.1+1, trace f size i s.2)) (0,[])).1

/-- Textbook rotation-system face count. The empty graph is an annulus. -/
def boundary {n} (D : Diagram n) (c : Sides n) : Nat :=
  if n = 0 then 2 else cycles (6*n) (face D c)

/-- Search positive distances in the circle's induced orientation. -/
def nextSame {n} (c : Sides n) (i : Nat) : Nat :=
  let candidates := (List.range (2*n)).map fun k =>
    if side c i then (i+2*n-(k+1)) % (2*n) else (i+k+1) % (2*n)
  (candidates.find? (fun j => side c j == side c i)).getD i

/-- Both unattached annulus circles contribute, including at n=0. -/
def emptyCircles {n} (c : Sides n) : Nat :=
  (if (List.range (2*n)).all (fun i => side c i) then 1 else 0) +
  (if (List.range (2*n)).all (fun i => !(side c i)) then 1 else 0)

def dartBoundary {n} (D : Diagram n) (c : Sides n) : Nat :=
  cycles (2*n) (fun i => nextSame c (mate D i)) + emptyCircles c

/-- No division or truncation: a genus is witnessed by the exact Euler equation. -/
def HasGenus {n} (D : Diagram n) (c : Sides n) (g : Nat) : Prop :=
  2*g + boundary D c = n+2

def genusRange {n} (D : Diagram n) : Set Nat := {g | ∃ c, HasGenus D c g}

def Range12 {n} (D : Diagram n) : Prop := ∀ g, genusRange D g ↔ g=1 ∨ g=2

def Range01 {n} (D : Diagram n) : Prop := ∀ g, genusRange D g ↔ g=0 ∨ g=1

/-- A cyclic shift or a reflection conjugates the endpoint pairing. This is
exactly rotation/reversal/renaming for the name-free involution encoding. -/
def Generator {n} (D E : Diagram n) : Prop :=
  ∃ e : Fin (2*n) ≃ Fin (2*n),
    ((∃ r : Nat, ∀ i, (e i).val = (i.val+r)%(2*n)) ∨
     (∃ r : Nat, ∀ i, (e i).val = (r+2*n-1-i.val)%(2*n))) ∧
    ∀ i, E.partner (e i) = e (D.partner i)

def Equivalent {n} : Diagram n → Diagram n → Prop := Relation.EqvGen Generator

instance diagramSetoid (n : Nat) : Setoid (Diagram n) where
  r := Equivalent
  iseqv := ⟨fun x => Relation.EqvGen.refl x, fun h => Relation.EqvGen.symm _ _ h, fun h k => Relation.EqvGen.trans _ _ _ h k⟩

/-- The named representative, specified literally by its pairing. -/
def IsRepresentative {n} (D : Diagram n) : Prop := ∀ i,
  (D.partner i).val = if i.val < 3 then i.val+3 else if i.val < 6 then i.val-3
    else if i.val % 2 = 0 then i.val+1 else i.val-1

end Chord
