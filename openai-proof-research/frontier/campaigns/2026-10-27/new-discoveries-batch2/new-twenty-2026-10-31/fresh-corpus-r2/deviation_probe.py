"""Exact finite sanity check of both ordinary Burnside constructions; not formal proof."""
from itertools import permutations
from fractions import Fraction
from math import lcm
from pathlib import Path
import json

def run(n,even_only=False):
 ps=list(permutations(range(n)))
 if even_only:ps=[p for p in ps if sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))%2==0]
 ix={p:i for i,p in enumerate(ps)};one=ix[tuple(range(n))];sz=len(ps)
 mul=[[ix[tuple(a[b[i]] for i in range(n))] for b in ps] for a in ps]
 inv=[next(j for j in range(sz) if mul[i][j]==one) for i in range(sz)]
 def closure(s):
  z=set(s)|{one}
  while True:
   zz=z|{mul[a][b] for a in z for b in z}
   if zz==z:return frozenset(z)
   z=zz
 def conj(K,g):return frozenset(mul[mul[g][x]][inv[g]] for x in K)
 subs={frozenset([one])};pending=list(subs)
 while pending:
  K=pending.pop()
  for g in range(sz):
   if g not in K:
    L=closure(K|{g})
    if L not in subs:subs.add(L);pending.append(L)
 subs=sorted(subs,key=lambda x:(-len(x),tuple(sorted(x))))
 rep={K:min(tuple(sorted(conj(K,g))) for g in range(sz)) for K in subs}
 records=[]
 for H in subs:
  fam={K for K in subs if any(conj(K,g)<=H for g in range(sz))}
  alpha={}
  for K in subs:alpha[K]=int(K in fam)-sum(v for L,v in alpha.items() if K<L)
  coeff={}
  for K in subs:coeff[rep[K]]=coeff.get(rep[K],Fraction(0))+Fraction(len(K)*alpha[K],sz)
  # Check all actual fixed-point marks from orbit coefficients, not just inverted poset data.
  for T in subs:
   mark=sum(c*Fraction(sum(T<=conj(frozenset(R),g) for g in range(sz)),len(R)) for R,c in coeff.items())
   assert mark==int(T in fam)
  assert all(alpha[K]==0 for K in subs if K not in fam)
  delta=lcm(*(v.denominator for v in coeff.values()))
  assert delta%(sz//len(H))==0 and sz%delta==0
  assert (delta==1)==(len(H)==sz)
  records.append({'H_order':len(H),'index':sz//len(H),'delta':delta})
 return {'group':('A' if even_only else 'S')+str(n),'order':sz,'subgroups':len(subs),'all_subgroups_checked':records}
if __name__=='__main__':
 r={'kind':'exact finite sanity checks only; general ordinary proof is in DEVIATION-PROOF.md; no Lean','groups':[run(3),run(4,True),run(4)]}
 Path(__file__).with_name('deviation-probe.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
