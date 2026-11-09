from pathlib import Path
import json
D=Path(__file__).resolve().parents[1];o=json.loads((D/'outputs/dprime-cycle.json').read_text());assert o['k']==21 and o['cycle_length']==24
s='''import Mathlib.Data.List.Range
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
'''
for i,(side,v) in enumerate(o['cycle']):s+=f"def v{i} : Vertex := ({'true' if side else 'false'},[{','.join(map(str,v))}])\n"
s+='def cycle : List Vertex := ['+','.join('v'+str(i) for i in range(24))+']\n'
s+='''theorem cycle_certificate : IsCycle 21 cycle := by decide
theorem cycle_length : cycle.length = 24 := by decide
theorem bound_value : Bound 21 = 26 := by decide
theorem source_refutation : ¬ SourceConjectureF3 := by
  intro h
  have hh := h 21 (by decide) cycle cycle_certificate
  rw [cycle_length, bound_value] at hh
  omega
#print axioms source_refutation
end DPrime
'''
(D/'lean/DPrime.lean').write_text(s)
