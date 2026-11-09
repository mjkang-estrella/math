import itertools,json,math,functools
pairs=[(0,1),(1,2),(0,2)]; singles=[0,2,1]
@functools.lru_cache(None)
def corr(h):
 rows=[2]*h[2]+[1]*h[1];n=sum(h);z=0
 # Compare rational a/b with 3/n; convention 0/0=0, positive/0=infty.
 def le(a,b):return (a==0) if b==0 else a*n<=3*b
 def gt(a,b):return (a>0) if b==0 else a*n>3*b
 for i,row in enumerate(rows):
  for x in range(row):
   a=row-x-1;l=sum(r>x for r in rows[i+1:])
   z+=int(le(a+1,l+1) and gt(a,l))-int(le(a,l) and gt(a+1,l+1))
 return z
# The source map's output rank inequality conflicts with its own pides; use the
# rank-decreasing pair convention consistent with input and pides, and label diagnostic.
def make(w,a,b):
 h=[0]*3
 for j,p in enumerate(w):
  for c in pairs[p] if j<a else [singles[p]]:h[c]+=1
 n=2*a+b
 if h[0]*3<n or (h[0]+h[1])*3<2*n:return
 counts=[0]*3;offset=[0,h[0],h[0]+h[1]];ranks=[]
 for j,p in enumerate(w):
  cs=list(pairs[p]) if j<a else [singles[p]]
  cs.sort(key=lambda c:3*(offset[c]+counts[c])-n*c,reverse=True)
  for c in cs:ranks.append(3*(offset[c]+counts[c])-n*c);counts[c]+=1
 for i in range(n-1):
  if (ranks[i]<ranks[i+1]) != (i%2==1 or i>=2*a-1):return
 return sum(0<ranks[j]-ranks[i]<3 for i in range(n) for j in range(i+1,n))+corr(tuple(h))
for L in range(1,11):
 tested=bad=0;by_n={};examples=[]
 for a in range(L+1):
  b=L-a;n=2*a+b
  if n%3==0:continue
  for w in itertools.product(range(3),repeat=L):
   v=make(w,a,b)
   if v is None:continue
   u=make(tuple(reversed(w)),b,a);tested+=1;by_n[n]=by_n.get(n,0)+1
   if v!=u:
    bad+=1
    if len(examples)<3:examples.append(dict(a=a,b=b,placements=w,original=v,switched=u))
 print(json.dumps(dict(objects=L,tested=tested,by_rows=by_n,diagnostic_mismatches=bad,examples=examples,scope='coprime part a, rank-decreasing convention; not Phi part b')),flush=True)
