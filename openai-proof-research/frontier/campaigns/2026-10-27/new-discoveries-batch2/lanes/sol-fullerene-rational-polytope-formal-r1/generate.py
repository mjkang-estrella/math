from pathlib import Path
from fractions import Fraction as F
import json
L=Path(__file__).resolve().parent
data=json.loads((L/'frozen/sol-fullerene-literal-feasibility-prior-r2--rational-realizations.json').read_text())
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def cross(a,b):return [a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]]
def rat(x):return f'({x.numerator} / {x.denominator} : ℝ)'
def vec(xs):return '!['+', '.join(xs)+']'
def lookup(xs):return '(fun i => match i.val with '+ ' '.join(f'| {i} => {x}' for i,x in enumerate(xs[:-1]))+' | _ => '+xs[-1]+')'
def add(xs):return xs[0] if len(xs)==1 else '('+xs[0]+' + '+add(xs[1:])+')'
for name,c in data.items():
 q=[[F(t) for t in row] for row in c['dual_vertices']]
 p=[[F(t) for t in row] for row in c['primal_vertices']]
 a,b,d=q[:3]; det=dot(a,cross(b,d)); assert det
 weights=[]
 for k in range(3):
  v=[cross(b,d)[k]/det,cross(d,a)[k]/det,cross(a,b)[k]/det]
  pair=[]
  for sign in [1,-1]:
   cs=[sign*x for x in v]+[F(0)]*29
   shift=max(F(0),-min(cs)); cs=[x+shift for x in cs]
   assert min(cs)>=0
   assert [sum(cs[i]*q[i][j] for i in range(32)) for j in range(3)]==[F(sign if j==k else 0) for j in range(3)]
   pair.append(cs)
  weights.append(pair)
 out='import Literal\nimport Mathlib.Tactic.FinCases\nset_option autoImplicit false\nset_option warningAsError true\nset_option maxRecDepth 4000\nnoncomputable section\nnamespace FullereneGeometry\n'
 out+=f'def q{name} : Fin 32 → E := '+lookup([lookup([rat(x) for x in row]) for row in q])+'\n'
 out+=f'def p{name} : Fin 60 → E := '+vec([vec([rat(x) for x in row]) for row in p])+'\n'
 out+=f'def w{name} (k : Fin 3) (s : Bool) : Fin 32 → ℝ :=\n  if s then '+lookup([lookup([rat(x) for x in pair[0]]) for pair in weights])+' k else '+lookup([lookup([rat(x) for x in pair[1]]) for pair in weights])+' k\n'
 out+=f'theorem w{name}_nonneg : ∀ k s i, 0 ≤ w{name} k s i := by\n  intro k s i\n  fin_cases k <;> cases s <;> fin_cases i <;> norm_num [w{name}]\n'
 for k in range(3):
  for s in ['true','false']:
   terms=[rat(weights[k][0 if s=='true' else 1][i])+' * '+add([rat(q[i][j])+f' * x {j}' for j in range(3)]) for i in range(32)]
   rhs=f'x {k}' if s=='true' else f'-x {k}'
   out+=f'theorem w{name}_coordinate_{k}_{s} (x : E) : (∑ i, w{name} {k} {s} i * dot (q{name} i) x) = '+rhs+f' := by\n  simp only [dot, Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]\n  change '+add(terms)+' = '+rhs+'\n  ring\n'
 out+=f'theorem w{name}_coordinate : ∀ k s x, (∑ i, w{name} k s i * dot (q{name} i) x) = (if s then x k else -x k) := by\n  intro k s x\n  fin_cases k <;> cases s\n'
 for k in range(3):
  for s in ['false','true']:
   out+=f'  · exact w{name}_coordinate_{k}_{s} x\n'
 out+=f'theorem compact_{name} : IsCompact (poly q{name}) := compact_of_positive_span q{name} w{name} w{name}_nonneg w{name}_coordinate\n'
 out+=f'theorem interior_{name} : (0 : E) ∈ interior (poly q{name}) := zero_interior q{name}\n'
 out+='end FullereneGeometry\n'
 (L/f'Instance{name}.lean').write_text(out)
 (L/f'positive-span-{name}.json').write_text(json.dumps([[[str(x) for x in cs] for cs in pair] for pair in weights],indent=2)+'\n')
 print(name,'generated real coordinate data and positive span certificate')
