import itertools,json,random,time
start=time.monotonic()
def spaces(r):
 seen={1};todo=[1]
 for s in todo:
  for x in range(1,1<<r):
   if not s>>x&1:
    t=s|sum(1<<(v^x) for v in range(1<<r) if s>>v&1)
    if t not in seen:seen.add(t);todo.append(t)
 return [(s,s.bit_count().bit_length()-1) for s in todo]
def det(a):
 if len(a)==1:return a[0][0]
 return sum((-1)**j*a[0][j]*det([row[:j]+row[j+1:] for row in a[1:]]) for j in range(len(a)))
def check(r,g,sp):
 flats={s&g:rank for s,rank in sp if (s&g).bit_count()>=rank}
 # assign actual ranks using minimum ambient subspace containing the intersection
 flats={f:min(k for s,k in sp if f&~s==0) for f in flats}
 R={};top=max(flats.values())
 for f,k in flats.items():
  row=tuple(sum(l==top-j and h&f==f for h,l in flats.items()) for j in range(top+1))
  cor=top-k
  if cor in R and R[cor]!=row:return None
  R[cor]=row
 mat=[R[i] for i in range(top+1)]
 for z in range(1,top+2):
  for rows in itertools.combinations(range(top+1),z):
   for cols in itertools.combinations(range(top+1),z):
    v=det([[mat[i][j] for j in cols] for i in rows])
    if v<0:return dict(negative=v,rows=rows,cols=cols,R=mat,ground=g)
 return True
for r in [2,3,4]:
 sp=spaces(r);gs=list(range(1,1<<( (1<<r)-1)))
 if r==4:random.Random(89).shuffle(gs);gs=gs[:2000]
 uniform=0;tested=0
 for g0 in gs:
  g=g0<<1;ans=check(r,g,sp);tested+=1
  if ans is not None:uniform+=1
  if isinstance(ans,dict):print(json.dumps(dict(counterexample=True,r=r,**ans)),flush=True);break
 else:print(json.dumps(dict(r=r,grounds=tested,upper_uniform=uniform,negative_minor=False)),flush=True)
