import itertools,json,pathlib,random,sys
L=pathlib.Path.cwd()
def plane(q):
 def mul(a,b):
  if q!=4:return a*b%q
  c=0
  while b:
   if b&1:c^=a
   b>>=1;a<<=1
   if a&4:a^=7
  return c
 def dot(a,b):
  xs=[mul(x,y) for x,y in zip(a,b)]
  return xs[0]^xs[1]^xs[2] if q==4 else sum(xs)%q
 pts=[(1,a,b) for a in range(q) for b in range(q)]+[(0,1,a) for a in range(q)]+[(0,0,1)]
 lines=[[i for i,p in enumerate(pts) if dot(p,u)==0] for u in pts];n=len(pts)
 assert all(len(x)==q+1 for x in lines)
 assert all(sum(i in line and j in line for line in lines)==1 for i in range(n) for j in range(i))
 assert all(len(set(a)&set(b))==1 for i,a in enumerate(lines) for b in lines[:i])
 return pts,lines

def controls():
 out=[]
 for q,r,mask in [(4,4,1299211),(5,4,70588740),(5,5,241579737)]:
  pts,ls=plane(q);full=(1<<len(pts))-1;lm=[sum(1<<i for i in line) for line in ls]
  def step(a):
   b=a
   for l in lm:
    if (a&l).bit_count()>=r:b|=l
   return b
  def close(a):
   hist=[a]
   while True:
    b=step(a)
    if b==a:return hist
    hist.append(b);a=b
  h=close(mask); dels={i:close(mask^(1<<i))[-1] for i in range(len(pts)) if mask>>i&1}
  assert h[-1]==full and all(b!=full for b in dels.values())
  out.append(dict(q=q,r=r,mask=mask,rounds=h,deletion_closures=dels))
 # bounded independent greedy searches at (7,6), (7,7); no absence inference
 rng=random.Random(333709)
 for r in [6,7]:
  pts,ls=plane(7);n=len(pts);full=(1<<n)-1;lm=[sum(1<<i for i in line) for line in ls];hist={}
  def close(a):
   t=0
   while True:
    b=a
    for l in lm:
     if (a&l).bit_count()>=r:b|=l
    if a==b:return a,t
    a=b;t+=1
  for _ in range(120):
   a=full;order=list(range(n));rng.shuffle(order)
   for i in order:
    if close(a^(1<<i))[0]==full:a^=1<<i
   end,t=close(a);assert end==full
   assert all(close(a^(1<<i))[0]!=full for i in range(n) if a>>i&1)
   hist[t]=hist.get(t,0)+1
  out.append(dict(q=7,r=r,trials=120,time_histogram=hist))
 (L/'controls.json').write_text(json.dumps(out,indent=2));print(out)

def encode():
 pts,ls=plane(5);n=len(pts);clauses=[];nv=0
 def var():
  nonlocal nv
  nv+=1;return nv
 def arr():return [var() for _ in range(n)]
 a=arr();x=arr();i=arr();j=arr();b=[arr() for _ in range(n)]
 def add(*xs):clauses.append(list(xs))
 def threshold(z,vs):
  # z iff >=5 out of 6 (both directions, unlike discovery)
  for pair in itertools.combinations(vs,2):add(-z,*pair)
  for five in itertools.combinations(vs,5):add(z,*[-v for v in five])
 for k,line in enumerate(ls):threshold(i[k],[a[p] for p in line]);threshold(j[k],[x[p] for p in line])
 for p in range(n):
  ors=[a[p]]+[i[k] for k,line in enumerate(ls) if p in line]
  add(-x[p],*ors)
  for z in ors:add(-z,x[p])
  add(x[p],*[j[k] for k,line in enumerate(ls) if p in line])
 add(*[-z for z in x])
 for v in range(n):
  add(-a[v],-b[v][v])
  for p in range(n):
   if p!=v:add(-a[v],-a[p],b[v][p])
  for line in ls:
   for p in line:add(b[v][p],*[-b[v][u] for u in line if u!=p])
 for p in [0,25,30]:add(a[p])
 (L/'independent.cnf').write_text(f'p cnf {nv} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
 print(dict(variables=nv,clauses=len(clauses)))
if sys.argv[1]=='controls':controls()
else:encode()
