import Mathlib.Data.List.Range
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace DPrime
abbrev Vertex := Bool × List (Fin 3)
def coordinate (a : List (Fin 3)) (i : Nat) : Int := ((a[i]?.getD 0).val : Int)
-- First coordinates are 1,11,12,21,22,22',23,32,33,33',34,43,...
-- The equations are exactly (2.8) of Mukherjee arXiv:2101.06743v1.
def equation (a b : List (Fin 3)) (j : Nat) : Int :=
  if j = 1 then coordinate a 1 - coordinate a 0 + coordinate b 1 - coordinate b 0 + coordinate a 0 * coordinate b 0
  else
    let t := if j < 4 then 1 else j-2
    coordinate a j + coordinate a t + coordinate b j + coordinate b t +
    if j % 4 = 0 ∨ j % 4 = 3 then coordinate a t * coordinate b 0
    else coordinate a 0 * coordinate b t
-- Int reduction modulo 3 is the standard concrete presentation of F_3.
def Adj (k : Nat) (v w : Vertex) : Prop :=
  v.2.length = k ∧ w.2.length = k ∧ v.1 ≠ w.1 ∧
  ∀ j ∈ List.range (k-1),
    (if v.1 then equation w.2 v.2 (j+1) else equation v.2 w.2 (j+1)) % 3 = 0
instance (k : Nat) (v w : Vertex) : Decidable (Adj k v w) :=
  inferInstanceAs (Decidable (v.2.length=k ∧ w.2.length=k ∧ v.1≠w.1 ∧ ∀ j ∈ List.range (k-1), (if v.1 then equation w.2 v.2 (j+1) else equation v.2 w.2 (j+1)) % 3=0))
def getVertex (C : List Vertex) (i : Nat) : Vertex := C[i]?.getD (false,[])
def IsCycle (k : Nat) (C : List Vertex) : Prop :=
  3 ≤ C.length ∧ C.Nodup ∧ ∀ i ∈ List.range C.length,
    Adj k (getVertex C i) (getVertex C ((i+1)%C.length))
instance (k : Nat) (C : List Vertex) : Decidable (IsCycle k C) :=
  inferInstanceAs (Decidable (3≤C.length ∧ C.Nodup ∧ ∀ i ∈ List.range C.length, Adj k (getVertex C i) (getVertex C ((i+1)%C.length))))
def Bound (k : Nat) : Nat := if k%2=0 then k+4 else k+5
-- The full all-k conjecture specialized to the admissible prime power q=3.
def SourceConjectureF3 : Prop := ∀ k : Nat, 2 ≤ k → ∀ C : List Vertex, IsCycle k C → Bound k ≤ C.length
def v0 : Vertex := (true,[2,1,0,2,0,1,1,1,1,2,1,1,2,2,1,1,1,2,1,2,1])
def v1 : Vertex := (false,[2,2,1,0,0,2,2,1,1,0,1,0,0,1,2,0,1,1,1,2,1])
def v2 : Vertex := (true,[0,0,0,1,2,1,1,2,2,2,1,1,1,2,1,0,2,2,1,1,0])
def v3 : Vertex := (false,[0,0,0,2,1,2,2,1,1,1,2,2,2,1,2,0,1,1,2,2,0])
def v4 : Vertex := (true,[2,2,1,2,1,0,2,2,0,2,0,2,1,1,1,2,1,0,2,1,1])
def v5 : Vertex := (false,[2,1,1,2,1,1,0,1,1,0,2,2,2,0,0,0,1,0,0,2,0])
def v6 : Vertex := (true,[1,0,1,2,2,0,2,0,0,2,0,2,0,1,1,2,1,0,2,1,1])
def v7 : Vertex := (false,[0,1,1,2,1,2,1,2,2,2,1,1,1,2,1,2,2,2,1,1,1])
def v8 : Vertex := (true,[0,2,2,1,2,1,2,1,1,1,2,2,2,1,2,1,1,1,2,2,2])
def v9 : Vertex := (false,[2,0,1,0,1,2,0,2,0,0,1,0,1,2,0,2,0,0,1,0,1])
def v10 : Vertex := (true,[1,1,2,2,1,1,2,2,1,1,2,2,1,1,2,2,1,1,2,2,1])
def v11 : Vertex := (false,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])
def v12 : Vertex := (true,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])
def v13 : Vertex := (false,[2,2,1,1,2,2,1,1,2,2,1,1,2,2,1,1,2,2,1,1,2])
def v14 : Vertex := (true,[2,1,0,1,1,0,0,2,1,0,0,2,1,0,0,2,1,0,0,2,1])
def v15 : Vertex := (false,[0,1,1,1,2,1,0,1,2,0,0,1,2,0,0,1,2,0,0,1,2])
def v16 : Vertex := (true,[1,0,1,0,1,1,0,2,1,0,0,2,1,0,0,2,1,0,0,2,1])
def v17 : Vertex := (false,[2,1,1,1,2,1,1,1,0,2,0,0,2,0,1,1,0,2,0,0,2])
def v18 : Vertex := (true,[2,2,1,0,0,1,0,1,0,0,0,0,1,0,0,2,0,0,0,0,1])
def v19 : Vertex := (false,[0,0,0,1,2,1,1,1,0,1,0,0,2,0,0,1,0,0,0,0,2])
def v20 : Vertex := (true,[1,1,2,1,2,0,1,0,0,1,0,0,1,0,0,2,0,0,0,0,1])
def v21 : Vertex := (false,[2,0,1,1,0,2,2,2,1,0,2,2,1,1,2,2,2,1,1,1,0])
def v22 : Vertex := (true,[0,2,2,0,0,0,1,2,2,1,0,0,0,0,0,0,2,0,0,1,2])
def v23 : Vertex := (false,[0,1,1,0,0,0,2,1,1,2,0,0,0,0,0,0,1,0,0,2,1])
def cycle : List Vertex := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23]
theorem cycle_certificate : IsCycle 21 cycle := by decide
theorem cycle_length : cycle.length = 24 := by decide
theorem bound_value : Bound 21 = 26 := by decide
theorem source_refutation : ¬ SourceConjectureF3 := by
  intro h
  have hh := h 21 (by decide) cycle cycle_certificate
  rw [cycle_length, bound_value] at hh
  omega
#print axioms source_refutation
end DPrime
