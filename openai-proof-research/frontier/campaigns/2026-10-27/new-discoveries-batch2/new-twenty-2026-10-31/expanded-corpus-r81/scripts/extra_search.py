from pathlib import Path
from math import isqrt,comb
import json,itertools
D=Path(__file__).resolve().parents[1];out={}
N=20000;mask=(1<<(N+1))-1;p=1
for k in range(1,N+1):
 if k%21==0:continue
 shift=k
 while shift<=N:p^=(p<<shift)&mask;shift*=2
q=json.loads((D/'outputs/sequence-search.json').read_text())['357344']['Q_primes'];rows=[]
for o in q:
 a=o['p'];n=(11*a*a-5)//6
 if n<=N:rows.append({'p':a,'n':n,'parity':(p>>n)&1})
out['357344']={'direct_b21_parity':'GF(2) ordinary restricted partition product for all degrees 0..20000','tested_Q_primes':rows}
def stack(p):
 if not p:return p
 k=p.index(max(p));return stack(p[:k])+stack(p[k+1:])+(p[k],)
rows=[]
for n in range(1,9):
 count=0
 for p in itertools.permutations(range(n)):
  for _ in range(3):p=stack(p)
  count+=p==tuple(range(n))
 rows.append({'n':n,'permutations':__import__('math').factorial(n),'W3':count})
out['342207']={'exact_counts':rows,'note':'Initial counts cannot refute asymptotic growth interval'}
a=[sum(2*comb(n+1,k-1)*comb(n+1,k)*comb(n+1,k+1) for k in range(1,n+1))//(n*(n+1)**2) for n in range(1,201)];rows=[]
for r in range(1,13):
 a=[a[i]*a[i+2]-a[i+1]**2 for i in range(len(a)-2)];rows.append({'r':r,'n_range':[1,len(a)],'negative_indices':[i+1 for i,x in enumerate(a) if x<0]})
out['368344']={'larger_sweep':rows}
(D/'outputs/extra-search.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
