import Mathlib.Tactic
namespace Delta153
abbrev Graph := List (List Nat)
def edge (g : Graph) (i j : Nat) : Nat := (g[i]?.getD [])[j]?.getD 0
def verts (g : Graph) := List.range g.length
def wye (g : Graph) (x : Nat) : Bool :=
  ((verts g).filter (fun i => edge g x i != 0)).length == 3 &&
  (verts g).all (fun i => edge g x i == 0 || edge g x i == 2)
def reduce (g : Graph) (x : Nat) : Graph :=
  let keep := (verts g).filter (fun i => i != x)
  keep.map fun i => keep.map fun j => edge g i j +
    (if i != j && edge g x i == 2 && edge g x j == 2 then 1 else 0)
def triangle (g : Graph) (a b c : Nat) : Bool :=
  a != b && a != c && b != c && edge g a b > 0 && edge g a c > 0 && edge g b c > 0
  && a < g.length && b < g.length && c < g.length
def expand (g : Graph) (a b c : Nat) : Graph :=
  let t := [a,b,c]
  ((verts g).map fun i => ((verts g).map fun j => edge g i j -
    (if i != j && t.contains i && t.contains j then 1 else 0)) ++
    [if t.contains i then 2 else 0]) ++ [(verts g).map (fun i => if t.contains i then 2 else 0) ++ [0]]
inductive Move : Graph → Graph → Prop
| down (g : Graph) (x : Nat) (h : wye g x = true) : Move g (reduce g x)
| up (g : Graph) (a b c : Nat) (h : triangle g a b c = true) : Move g (expand g a b c)
inductive Reach : Graph → Graph → Prop
| refl (g : Graph) : Reach g g
| step {g h k : Graph} : Move g h → Reach h k → Reach g k
def original : Graph := [[0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0]]
def p0 : Graph := original
def p1 : Graph := reduce p0 0
def p2 : Graph := reduce p1 0
def p3 : Graph := reduce p2 3
def p4 : Graph := reduce p3 4
def p5 : Graph := reduce p4 6
def p6 : Graph := reduce p5 7
def p7 : Graph := reduce p6 11
def Gprime : Graph := p7
theorem Gprime_literal : Gprime = [[0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3], [0, 0, 0, 1, 1, 0, 1, 0, 3, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0], [0, 1, 2, 0, 0, 0, 2, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 2, 1, 1, 1, 0], [2, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1], [0, 1, 0, 2, 2, 0, 0, 0, 1, 0, 0], [1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], [0, 3, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 1, 1, 0, 1, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0]] := by decide
def q0 : Graph := Gprime
def q1 : Graph := expand q0 0 5 7
def q2 : Graph := expand q1 1 6 8
def q3 : Graph := reduce q2 6
def q4 : Graph := reduce q3 10
def q5 : Graph := expand q4 4 7 10
def q6 : Graph := expand q5 3 7 10
def q7 : Graph := reduce q6 10
def q8 : Graph := reduce q7 7
def q9 : Graph := reduce q8 9
theorem explicit_reduction : Reach Gprime q9 := by
  apply Reach.step (Move.up q0 0 5 7 (by decide))
  apply Reach.step (Move.up q1 1 6 8 (by decide))
  apply Reach.step (Move.down q2 6 (by decide))
  apply Reach.step (Move.down q3 10 (by decide))
  apply Reach.step (Move.up q4 4 7 10 (by decide))
  apply Reach.step (Move.up q5 3 7 10 (by decide))
  apply Reach.step (Move.down q6 10 (by decide))
  apply Reach.step (Move.down q7 7 (by decide))
  apply Reach.step (Move.down q8 9 (by decide))
  exact Reach.refl _
theorem order_drop : q9.length < Gprime.length := by decide
def endpoint (g : Graph) (i : Nat) : Bool :=
  ((verts g).filter (fun j => edge g i j == 1)).length == 2 &&
  ((verts g).filter (fun j => edge g i j == 2)).length == 2
def internal (g : Graph) (i : Nat) : Bool :=
  ((verts g).filter (fun j => edge g i j == 1)).length == 4 &&
  ((verts g).filter (fun j => edge g i j == 2)).length == 1
def endpointBlocked (g : Graph) : Bool := (verts g).all fun i => !endpoint g i ||
  (verts g).all fun j => !(endpoint g j || internal g j) ||
  (verts g).all fun k => !(i != j && i != k && j != k && edge g i j == 1 && edge g i k == 1 && edge g j k == 1)
theorem endpoints_blocked : endpointBlocked Gprime = true := by decide
-- Diagnostic recursive checker. Its soundness bridge and source-chain bridge are NOT yet formalized.
def pureLower : Nat → Nat → Graph → Bool
| 0,b,g => b <= g.length && (verts g).all (fun x => !wye g x)
| f+1,b,g => b <= g.length && (verts g).all (fun x => !wye g x || pureLower f b (reduce g x))
#print axioms explicit_reduction
#print axioms order_drop
#print axioms endpoints_blocked
end Delta153
