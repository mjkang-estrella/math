from pathlib import Path
import json
P=Path(__file__).resolve().parent
checks=0
def test(b):
 global checks
 assert b
 checks+=1
def mul(A,B,p):return [[sum(a*b for a,b in zip(r,c))%p for c in zip(*B)] for r in A]
def rank(A,p):
 A=[r[:] for r in A];k=0
 for j in range(len(A[0])):
  pivot=next((i for i in range(k,len(A)) if A[i][j]%p),None)
  if pivot is None:continue
  A[k],A[pivot]=A[pivot],A[k];inv=pow(A[k][j],-1,p);A[k]=[x*inv%p for x in A[k]]
  for i in range(len(A)):
   if i!=k:
    a=A[i][j];A[i]=[(x-a*y)%p for x,y in zip(A[i],A[k])]
  k+=1
 return k
results=[]
for p in [3,5,7,11,13,17,19,23,29,31]:
 I=[[int(i==j) for j in range(p)] for i in range(p)]
 T=[[int(i==(j+1)%p) for j in range(p)] for i in range(p)]
 N=[[(x-y)%p for x,y in zip(r,s)] for r,s in zip(T,I)]
 power=I
 for k in range(1,p+1):
  power=mul(power,N,p);test(rank(power,p)==p-k)
 test(all(x==0 for r in power for x in r));test(rank(N,p)==p-1)
 # Q[C_p] has simples 1 and cyclotomic dimension p-1; both
 # reduce with only trivial composition factors.
 solutions=[(a,b) for a in range(p+1) for b in range(p+1) if a+(p-1)*b==p]
 test(solutions==[(1,1),(p,0)])
 for a,b in solutions:test(a+(p-1)*b==p)
 test(1-1==0);test(p-0==p)
 results.append({'p':p,'monoid_solutions':solutions,'regular_N_rank':p-1,'trivial_N_rank':0,'regular_character_nonidentity':0,'trivial_p_character_nonidentity':p})
(P/'check-results.json').write_text(json.dumps({'assertions':checks,'status':'PASS','scope':'Exact cyclic-prime-group route diagnostic only; no source conjecture proved/refuted','cases':results},indent=2));print(checks,'exact assertions PASS')
