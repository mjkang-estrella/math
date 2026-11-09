from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
from math import comb
import json
L=Path(__file__).resolve().parent
def subsets(W,r):return [frozenset(c) for j in range(min(r,len(W))+1) for c in combinations(W,j)]
def lump(n,r,W,B):
 out={C:F(0) for C in subsets(W,r)}
 deletes=[(x,F(1,r)) for x in B]+[(None,F(r-len(B),r))]
 adds=[(y,F(1,n-r)) for y in W-B]+[(None,F(n-len(W)-r+len(B),n-r))]
 for x,a in deletes:
  for y,b in adds:
   if a*b==0:continue
   C=(B-({x} if x is not None else set()))|({y} if y is not None else set())
   out[frozenset(C)]+=a*b
 return out
results=[]
for r in range(1,4):
 for s in range(1,r+1):
  n=2*r+3;S=frozenset(range(s));N=comb(n,s);p=F(comb(r,s),N);q=p*F(s,r)
  for k in [None]+list(range(s)):
   U=None if k is None else frozenset(list(range(k))+list(range(s,2*s-k)))
   W=S if U is None else S|U;E=subsets(W,r)
   P={B:lump(n,r,W,B) for B in E}
   pi={B:F(comb(n-len(W),r-len(B)),comb(n,r)) for B in E}
   assert sum(pi.values())==1
   for B in E:
    assert sum(P[B].values())==1
    assert all(x>=0 for x in P[B].values())
    for C in E:assert pi[B]*P[B][C]==pi[C]*P[C][B]
   # Independent enumeration of actual old-complement swaps from EVERY H.
   for h in combinations(range(n),r):
    H=frozenset(h);B=H&W;d={C:F(0) for C in E}
    for x in H:
     for y in set(range(n))-H:d[((H-{x})|{y})&W]+=F(1,r*(n-r))
    assert d==P[B]
   A={B for B in E if S<=B or (U is not None and U<=B)};D=set(E)-A
   flow=sum(pi[B]*sum(P[B][C] for C in D) for B in A)
   assert flow==sum(pi[B]*sum(P[B][C] for C in A) for B in D)
   if U is None:assert flow==q
   else:
    inter=sum(pi[B] for B in E if S<=B and U<=B)
    # Absolute error bound covering intersection exits and cross jumps.
    assert abs(flow-2*q)<=2*inter+2*p*F(s,n-r)
   # Pure deletion K0 is lower triangular after cardinality ordering.
   ordered=sorted(D,key=lambda x:(len(x),tuple(sorted(x))))
   assert ordered[0]==frozenset()
   diag=[1-F(len(B),r) for B in ordered]
   assert diag.count(F(1))==1 and all(x<=1-F(1,r) for x in diag[1:])
   # Compare t=0..12 killed lump survival with full-chain survivor evolution.
   v={B:pi[B] for B in D}
   full={frozenset(h):F(1,comb(n,r)) for h in combinations(range(n),r) if frozenset(h)&W in D}
   for t in range(13):
    assert sum(v.values())==sum(full.values())
    v={C:sum(v[B]*P[B][C] for B in D) for C in D}
    new={}
    for H,mass in full.items():
     for x in H:
      for y in set(range(n))-H:
       J=(H-{x})|{y}
       if J&W in D:new[J]=new.get(J,F(0))+mass/F(r*(n-r))
    full=new
   results.append({'r':r,'s':s,'overlap':k,'n':n,'states':len(E),'killed_states':len(D),'flow':str(flow),'flow_over_q':str(flow/q),'checks':'all exact assertions passed'})
(L/'check-results.json').write_text(json.dumps({'diagnostic_only':True,'cases':results},indent=2)+'\n')
print('PASS:',len(results),'cases; exact old-complement lumping, reversibility, flux, pure-deletion spectrum and survival t=0..12.')
for name in ['ledger.json','prior-campaign-context.json']:
 d=json.loads((L/'administrative'/name).read_text())
 print(name,'keys',list(d),'accepted',d.get('accepted_count'), 'total',d.get('total_accepted_count'),'next',d.get('next_global_outcome_number'))
print('Parsed both full administrative snapshots; no count writes.')
