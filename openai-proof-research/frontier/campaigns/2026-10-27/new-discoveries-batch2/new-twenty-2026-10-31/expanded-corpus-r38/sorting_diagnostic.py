from itertools import product
import json
from pathlib import Path
H=Path(__file__).resolve().parent

def parts(n):
 for mask in range(1<<(n-1)):
  a=[]; last=0
  for j in range(1,n):
   if mask>>(j-1)&1:a.append(j-last);last=j
  yield a+[n-last]
def perm(a):
 n=sum(a);out=[]
 for k in a:out+=list(range(n-k+1,n+1));n-=k
 return out
def blocks(p,up):
 a=0
 for j in range(1,len(p)):
  if (p[j]>p[j-1])!=up:yield a,j;a=j
 yield a,len(p)
def step(p):return [x for a,b in blocks(p,False) for x in p[a:b][::-1]]
def cost(p):
 n=len(p);q=p[:]
 for j in range(n):
  if q==sorted(q):return j
  q=step(q)
 raise ValueError(p)
def pred(p):
 n=len(p)
 return n-2 if n%2 and any(b-a>=3 and a+b==n+1 for up in [True,False] for a,b in blocks(p,up)) else n-1
# indices are zero-based half-open: middle position is (n-1)/2, center iff a+b=n
# correct predicate uses a+b=n, not n+1

def pred(p):
 n=len(p)
 return n-2 if n%2 and any(b-a>=3 and a+b==n for up in [True,False] for a,b in blocks(p,up)) else n-1
out=[]
for n in range(3,15):
 c=0;bad=[]
 for a in parts(n):
  if len(a)==1 or len(a)==n:continue
  p=perm(a);x=cost(p);y=pred(p);c+=1
  if x!=y:bad.append({'parts':a,'actual':x,'predicted':y})
 out.append({'n':n,'checked':c,'failures':bad});print(out[-1],flush=True)
# Structured larger families: all two runs, all three runs up to n=45.
for n in [17,25,33,45]:
 c=0;bad=[]
 for a in range(1,n):
  for b in range(0,n-a):
   v=[a,n-a] if b==0 else [a,b,n-a-b];p=perm(v);c+=1
   if cost(p)!=pred(p):bad.append(v)
 print({'structured_n':n,'checked':c,'failures':bad},flush=True)
(H/'sorting-diagnostic.json').write_text(json.dumps(out,indent=2)+'\n')
