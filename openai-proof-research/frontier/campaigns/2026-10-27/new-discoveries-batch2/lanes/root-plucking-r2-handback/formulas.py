from structured import calc,build,chain,uni
from functools import lru_cache
from pathlib import Path
import json

def add(a,b,k=0):
 out=list(a)+[0]*max(0,len(b)+k-len(a))
 for i,x in enumerate(b):out[i+k]+=x
 return tuple(out)
def mul(a,b):
 out=(0,)
 for i,x in enumerate(b):
  if x:out=add(out,tuple(x*y for y in a),i)
 return out
@lru_cache(None)
def G(n,k):
 if k<0 or k>n or n<0:return (0,)
 if k==0 or k==n:return (1,)
 return add(G(n-1,k),G(n-1,k-1),n-k)
def formula(a,b,c,r,s):
 if r-1>b or s-1>a+b:return (0,)
 return (0,)*(c*(s-1))+mul(G(a+b+c-s+1,c),G(a+b-r+1,a))
def finite_sum(a,b,c,r,s):
 if r-1>b or s-1>a+b:return (0,)
 h=s-r;bp=b-s+1;out=(0,)
 for i in range(max(0,-bp),min(a,h)+1):
  term=mul(G(h,i),mul(G(a+bp+c,c),G(a+bp,a-i)))
  out=add(out,term,c*(s-1)+i*(bp+i))
 return out
# Small exact diagnostic of a universally derived identity, not finite certification.
rows=[]
for a,b,c,r,s in [(1,1,1,1,1),(8,1,2,1,3),(2,7,1,5,8),(3,2,4,2,4),(1,4,6,4,6),(9,2,1,3,10),(4,4,3,2,7),(2,2,2,4,4),(2,2,2,1,6),(3,2,2,2,3)]:
 p,leaves=build([chain(a),chain(b),chain(c)])
 q,_=calc(p,dict(zip(leaves,(r,1,s))));f=formula(a,b,c,r,s);g=finite_sum(a,b,c,r,s)
 assert q==f==g,(a,b,c,r,s,q,f,g)
 rows.append(dict(a=a,b=b,c=c,r=r,s=s,Q=q,unimodal=uni(q)))
Path('formula-checks.json').write_text(json.dumps(rows,indent=2));print('three-path identities: 10 PASS')
