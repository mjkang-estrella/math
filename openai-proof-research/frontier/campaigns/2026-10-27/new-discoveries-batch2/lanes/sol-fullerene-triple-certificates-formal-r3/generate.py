from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
from math import lcm
import json
L=Path(__file__).resolve().parent
raw=json.loads((L/'frozen/rational-realizations.json').read_text())
def v(a):return '(⟨'+', '.join('('+str(x)+')' for x in a)+'⟩ : V)'
def point(p):return '(⟨'+v(p[:3])+', ('+str(p[3])+')⟩ : Point)'
def dt(a,b,c):return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])
def dp(a,b):return sum(x*y for x,y in zip(a,b))
coverage={}
for tag in ['G','H']:
 q=[[F(x) for x in r] for r in raw[tag]['dual_vertices']]
 p=[[F(x) for x in r] for r in raw[tag]['primal_vertices']]
 D=lcm(*(x.denominator for r in q for x in r));A=[[int(x*D) for x in r] for r in q]
 P=[]
 for r in p:
  d=lcm(*(x.denominator for x in r));P.append([int(x*d) for x in r]+[d])
 def table(items,fmt):return '(fun i => match i.val with '+''.join('| '+(str(h) if h<len(items)-1 else '_')+' => '+fmt(a)+' ' for h,a in enumerate(items))+')'
 data=['import IntegerCore','namespace TripleCertificates',f'def D{tag} : ℤ := {D}',f'def A{tag} : Fin 32 → V := '+table(A,v),f'def P{tag} : Fin 60 → Point := '+table(P,point),'end TripleCertificates']
 (L/f'Data{tag}.lean').write_text('\n'.join(data)+'\n')
 entries=[];modules=[]
 for n,(i,j,k) in enumerate(combinations(range(32),3)):
  a,b,c=[q[t] for t in [i,j,k]];det=dt(a,b,c)
  if not det:raise ValueError(('singular',tag,i,j,k))
  z=[]
  for coord in range(3):
   rows=[[F(1) if h==coord else r[h] for h in range(3)] for r in [a,b,c]]
   z.append(dt(*rows)/det)
  den=lcm(*(x.denominator for x in z));Z=[int(x*den) for x in z]+[den]
  violations=[t for t,r in enumerate(q) if dp(r,z)>1]
  if violations:kind='bad';w=violations[0];conclusion=f'bad (A{tag} {i}) (A{tag} {j}) (A{tag} {k}) (A{tag} {w}) D{tag} {point(Z)}'
  else:kind='good';w=p.index(z);conclusion=f'good (A{tag} {i}) (A{tag} {j}) (A{tag} {k}) D{tag} {point(Z)} (P{tag} {w})'
  entries.append(dict(n=n,i=i,j=j,k=k,kind=kind,witness=w,point=Z))
  if n%16==0:
   name=f'Batch{tag}{n//16:03d}';modules.append(name)
   out=[f'import Data{tag}','set_option maxRecDepth 10000','set_option maxHeartbeats 800000','namespace TripleCertificates']
  if n%16==0:recs=[]
  recs.append(f'⟨{i}, {j}, {k}, {point(Z)}, '+('true' if kind=='good' else 'false')+f', {w if kind=="good" else 0}, {w if kind=="bad" else 0}⟩')
  if n%16==15 or n==4959:
   out += [f'noncomputable def records{tag}{n//16:03d} : List Certificate := ['+', '.join(recs)+']',f'theorem checked{tag}{n//16:03d} : ∀ r ∈ records{tag}{n//16:03d}, checked A{tag} D{tag} P{tag} r := by decide +kernel']
   (L/f'{name}.lean').write_text('\n'.join(out+['end TripleCertificates'])+'\n')
 coverage[tag]=dict(D=D,entries=entries,modules=modules)
(L/'coverage.json').write_text(json.dumps(coverage,indent=2)+'\n')
print('generated 4960 per graph; rational Cramer computations are untrusted proof inputs')
