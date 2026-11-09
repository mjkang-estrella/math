import pathlib,itertools,json
W=pathlib.Path(__file__).resolve().parents[1]
exec((W/'scripts/compute.py').read_text().split('rows=[];counts={}')[0])
n=16;A=graph(n,[1,3,8]);witness={}
def visit(p):
 for t in itertools.combinations(p[:-1],2):
  t=(*t,p[-1])
  for delta in range(n):
   key=tuple(sorted((x+delta)%n for x in t));witness.setdefault(key,[(x+delta)%n for x in p])
 return len(witness)==560
paths(A,visit);assert len(witness)==560
# All unordered triples are explicitly covered by induced paths, with no path-length cutoff assumptions.
rows=[witness[t] for t in itertools.combinations(range(16),3)]
text="""import Circulant
open Circulant350979
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
namespace ReviewerControl
abbrev V16 := Fin 16
def R (a b : V16) : Prop := (b.val+16-a.val)%16 ∈ ([1,3,8,13,15] : List Nat)
instance (a b : V16) : Decidable (R a b) := inferInstanceAs (Decidable ((b.val+16-a.val)%16 ∈ ([1,3,8,13,15] : List Nat)))
def witnesses : List (List V16) := ["""+','.join('['+','.join(map(str,p))+']' for p in rows)+"]\n"
text+="""def valid (p : List V16) : Prop := p.Nodup ∧ ∀ i : Fin p.length, ∀ j : Fin p.length,
 R p[i] p[j] ↔ i.val+1=j.val ∨ j.val+1=i.val
instance (p : List V16) : Decidable (valid p) := inferInstanceAs (Decidable (p.Nodup ∧ ∀ i : Fin p.length, ∀ j : Fin p.length, R p[i] p[j] ↔ i.val+1=j.val ∨ j.val+1=i.val))
example : ∀ p ∈ witnesses, valid p := by decide
example : ∀ a b c : V16, a < b → b < c → ∃ p ∈ witnesses, a ∈ p ∧ b ∈ p ∧ c ∈ p := by decide
example : ∀ b : V16, b=0 ∨ R 0 b ∨ ∃ c : V16, R 0 c ∧ R c b := by decide
example : ¬ R 0 2 := by decide
end ReviewerControl
"""
(W/'extracted/Control16.lean').write_text(text)
