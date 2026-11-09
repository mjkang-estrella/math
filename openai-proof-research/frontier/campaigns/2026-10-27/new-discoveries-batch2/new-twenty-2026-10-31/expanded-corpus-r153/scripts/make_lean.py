import pathlib,json
L=pathlib.Path(__file__).resolve().parents[1];r=json.loads((L/'outputs/delta-trace-checked.json').read_text());exec((L/'scripts/delta.py').read_text().split('out=[]')[0])
s='''import Mathlib.Tactic
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
'''
def lit(x):return str(x)
s+='def original : Graph := '+lit(r['original'])+'\n'
A=r['original'];sequence=[('down',x) for x in r['pure_reduction_sequence']];start=0
s+='def p0 : Graph := original\n'
for i,(_,x) in enumerate(sequence):s+=f'def p{i+1} : Graph := reduce p{i} {x}\n'
s+=f'def Gprime : Graph := p{len(sequence)}\n'
s+='theorem Gprime_literal : Gprime = '+lit(r['Gprime'])+' := by decide\n'
s+='def q0 : Graph := Gprime\n'
for i,(op,arg) in enumerate(r['loop_erased_operations']):
 s+=f'def q{i+1} : Graph := '+(f'reduce q{i} {arg}' if op=='reduce' else f'expand q{i} '+ ' '.join(map(str,arg)))+'\n'
s+='theorem explicit_reduction : Reach Gprime q9 := by\n'
for i,(op,arg) in enumerate(r['loop_erased_operations']):
 s+='  apply Reach.step (Move.'+('down '+f'q{i} {arg}' if op=='reduce' else 'up '+f'q{i} '+' '.join(map(str,arg)))+' (by decide))\n'
s+='  exact Reach.refl _\n'
s+='theorem order_drop : q9.length < Gprime.length := by decide\n'
s+='def endpoint (g : Graph) (i : Nat) : Bool :=\n  ((verts g).filter (fun j => edge g i j == 1)).length == 2 &&\n  ((verts g).filter (fun j => edge g i j == 2)).length == 2\n'
s+='def internal (g : Graph) (i : Nat) : Bool :=\n  ((verts g).filter (fun j => edge g i j == 1)).length == 4 &&\n  ((verts g).filter (fun j => edge g i j == 2)).length == 1\n'
s+='def endpointBlocked (g : Graph) : Bool := (verts g).all fun i => !endpoint g i ||\n  (verts g).all fun j => !(endpoint g j || internal g j) ||\n  (verts g).all fun k => !(i != j && i != k && j != k && edge g i j == 1 && edge g i k == 1 && edge g j k == 1)\n'
s+='theorem endpoints_blocked : endpointBlocked Gprime = true := by decide\n'
s+='-- Diagnostic recursive checker. Its soundness bridge and source-chain bridge are NOT yet formalized.\n'
s+='def pureLower : Nat → Nat → Graph → Bool\n| 0,b,g => b <= g.length && (verts g).all (fun x => !wye g x)\n| f+1,b,g => b <= g.length && (verts g).all (fun x => !wye g x || pureLower f b (reduce g x))\n'
s+='#print axioms explicit_reduction\n#print axioms order_drop\n#print axioms endpoints_blocked\nend Delta153\n'
(L/'lean/Delta153.lean').write_text(s)
