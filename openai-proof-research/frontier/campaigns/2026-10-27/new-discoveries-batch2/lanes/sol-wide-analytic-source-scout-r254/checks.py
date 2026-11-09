from pathlib import Path
from fractions import Fraction as F
from math import comb
from itertools import combinations,permutations
import json
l=Path(__file__).resolve().parent
cases=[]
for r in range(1,4):
 for s in range(1,r+1):
  for overlap in [None]+list(range(s)):
   W=set(range(s if overlap is None else 2*s-overlap));S=set(range(s));U=None if overlap is None else set(range(overlap))|set(range(s,2*s-overlap))
   states=[frozenset(c) for j in range(min(r,len(W))+1) for c in combinations(sorted(W),j)];index={b:i for i,b in enumerate(states)}
   for n in [12,24]:
    P=[[F(0) for _ in states] for _ in states]
    for B in states:
     deletions=[(x,F(1,r)) for x in B]+[(None,F(r-len(B),r))]
     adds=[(y,F(1,n-r)) for y in W-B]+[(None,F(n-len(W)-r+len(B),n-r))]
     for x,a in deletions:
      for y,b in adds:
       C=set(B)
       if x is not None:C.remove(x)
       if y is not None:C.add(y)
       if a*b:P[index[B]][index[frozenset(C)]]+=a*b
    pi=[F(comb(n-len(W),r-len(B)),comb(n,r)) for B in states]
    assert sum(pi)==1 and all(sum(row)==1 for row in P)
    assert all(pi[i]*P[i][j]==pi[j]*P[j][i] for i in range(len(states)) for j in range(len(states)))
    A=[i for i,B in enumerate(states) if S<=B or (U is not None and U<=B)]
    flux=sum(pi[i]*sum(P[i][j] for j in range(len(states)) if j not in A) for i in A)
    q=F(s,r)*F(comb(r,s),comb(n,s))
    if U is None:assert flux==q
    else:assert abs(flux-2*q)<=2*F(comb(n-len(S|U),r-len(S|U)) if len(S|U)<=r else 0,comb(n,r))+2*F(comb(r,s),comb(n,s))*F(s,n-r)
    cases.append({'r':r,'s':s,'overlap':overlap,'n':n,'states':len(states),'flow_over_q':str(flux/q)})
quant=0
for k in range(2,7):
 for perm in permutations([F(1,2**j) for j in range(1,k)]):
  for n in [k+2,k+3]:
   masses=list(perm)+[F(1,2**j) for j in range(k,n+1)];upper=F(2**max(3-n,0),3*2**max(n-3,0))
   for j in range(1,n-2):
    p,q=masses[j-1:j+1];assert p*q/(p+q)>=upper
   quant+=1
(l/'check-results.json').write_text(json.dumps({'status':'PASS','lump_cases':cases,'quantization_cases':quant,'role':'finite support only; PROOF.md is analytic, not inferred from checks'},indent=2))
print('PASS',len(cases),'exact lump/flow cases;',quant,'quantization parameter cases')
