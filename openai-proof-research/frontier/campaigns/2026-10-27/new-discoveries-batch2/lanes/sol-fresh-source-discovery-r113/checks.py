import json
from pathlib import Path
def mul(a,b,n):
 rows=[(b>>(i*n))&((1<<n)-1) for i in range(n)];out=0
 for i in range(n):
  r=0
  for k in range(n):
   if a>>(i*n+k)&1:r^=rows[k]
  out|=r<<(i*n)
 return out
def power(a,k,n):
 r=sum(1<<(i*n+i) for i in range(n))
 for _ in range(k):r=mul(r,a,n)
 return r
results=[]
for n in (2,3):
 xs=range(1<<(n*n));ids=[a for a in xs if mul(a,a,n)==a];nils=[a for a in xs if power(a,n,n)==0]
 assert {e^q for e in ids for q in nils}==set(xs)
 assert set(nils)<={e^f for e in ids for f in ids}
 for e in ids:
  for f in ids:
   q=e^f
   assert mul(e,q,n)^mul(q,e,n)==q^mul(q,q,n)
 results.append({'n':n,'elements':len(xs),'idempotents':len(ids),'nilpotents':len(nils),'nil_clean':True,'nilpotent_difference_property':True,'anticommutator_pairs':len(ids)**2})
for n in (3,5,8,16):
 d=sum(1<<(i*n+i) for i in range(0,n,2));j=sum(1<<(i*n+i+1) for i in range(n-1))
 e=d^sum(1<<(i*n+i+1) for i in range(0,n-1,2));f=d^sum(1<<(i*n+i+1) for i in range(1,n-1,2))
 assert mul(e,e,n)==e and mul(f,f,n)==f and e^f==j
 assert power(j,n,n)==0 and power(j,n-1,n)!=0
 if n>=5:assert power(j,4,n)!=0 and not(mul(mul(e,f,n),e,n)==e and mul(mul(f,e,n),f,n)==f)
 results.append({'jordan_size':n,'e':str(e),'f':str(f),'j':str(j),'nilpotence_index':n,'q4_nonzero':power(j,4,n)!=0})
print(json.dumps({'status':'PASS','scope':'Exact finite diagnostics and route obstructions only; not a source resolution','results':results},indent=2))
