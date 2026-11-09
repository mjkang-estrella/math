# Plan A: leaves = top t^n labels, all parents-of-leaves share colour c (> m),
# upper rows colours in leaf-label range and proper. Local search over upper assignment.
# Usage: planA.py t n seconds seed
import sys,random,json,time
t,n,secs,seed=map(int,sys.argv[1:5]); random.seed(seed)
q=t**(n-1); N=sum(t**h for h in range(1,n)); m=N+t**n
# pair sums: sums in [2q+1-q/2, 2q+1+q/2] minus 2q+1, from a pairing of [1,2q] -- find by DFS
def pairing(q):
  target=set(range(2*q+1-q//2,2*q+2+q//2))-{2*q+1}
  used=[False]*(2*q+1); res=[]
  def dfs(rem):
    i=next((x for x in range(1,2*q+1) if not used[x]),None)
    if i is None: return True
    used[i]=True
    for j in range(2*q,i,-1):
      if not used[j] and (i+j) in rem:
        used[j]=True; res.append((i,j))
        if dfs(rem-{i+j}): return True
        res.pop(); used[j]=False
    used[i]=False; return False
  assert dfs(frozenset(target)); return res
P=pairing(q)
# leaf block [N+1, N+tq] split into t blocks of size q; outer blocks reverse-paired, middle two blocks via P
blocks=[list(range(N+1+b*q,N+1+(b+1)*q)) for b in range(t)]
tuples=[]
for i,(a,b) in enumerate(P):
  tup=[]
  for bb in range(t//2-1):
    tup+= [blocks[bb][i], blocks[t-1-bb][q-1-i]]
  off=N+(t//2-1)*q
  tup+=[off+a,off+b]; tuples.append(tup)
sums=[sum(x) for x in tuples]; assert len(set(sums))==q
best=None
for y in range(1,N-q+1):  # E = c - sums placed so min(E)=y
  c=max(sums)+y; E=[c-s for s in sums]
  if max(E)>N: break
  U=sorted(set(range(1,N+1))-set(E))
  # tree structure: rows; level h edges = t^h; we assign: E to level n-1 grouped t per row n-2 vertex,
  # U to levels 1..n-2. Represent per-level label lists.
  sizes=[t**h for h in range(1,n-1)]
  assert sum(sizes)==len(U)
  lo,hi=N+1,m
  def colours(levels,Eg):
    # levels[h-1] list of t^h labels; vertex j of row h has parent label levels[h-1][j] (h>=1)
    # children of row h vertex j: level h+1 indices j*t..j*t+t-1
    cols=[]
    for h in range(0,n-1):
      row=[]
      for j in range(t**h):
        p=levels[h-1][j] if h>=1 else 0
        if h+1<=n-2: ch=sum(levels[h][j*t:(j+1)*t])
        else: ch=sum(Eg[j*t:(j+1)*t])
        row.append(p+ch)
      cols.append(row)
    return cols
  def cost(levels,Eg):
    cols=colours(levels,Eg); bad=0
    for h,row in enumerate(cols):
      for j,w in enumerate(row):
        if w<lo: bad+=lo-w
        if w>hi: bad+=w-hi
        if h>=1 and w==cols[h-1][j//t]: bad+=1
    return bad
  flat=U[:]; random.shuffle(flat)
  levels=[]; k=0
  for s in sizes: levels.append(flat[k:k+s]); k+=s
  Eg=E[:]; random.shuffle(Eg)
  cur=cost(levels,Eg); start=time.time()
  pos=[(h,i) for h in range(len(sizes)) for i in range(sizes[h])]
  while cur>0 and time.time()-start<secs/ max(1,(N-q)):
    if random.random()<0.5 or not pos:
      i,j=random.randrange(q),random.randrange(q); Eg[i],Eg[j]=Eg[j],Eg[i]; c2=cost(levels,Eg)
      if c2<=cur: cur=c2
      else: Eg[i],Eg[j]=Eg[j],Eg[i]
    else:
      (h1,i1),(h2,i2)=random.choice(pos),random.choice(pos)
      levels[h1][i1],levels[h2][i2]=levels[h2][i2],levels[h1][i1]; c2=cost(levels,Eg)
      if c2<=cur: cur=c2
      else: levels[h1][i1],levels[h2][i2]=levels[h2][i2],levels[h1][i1]
  if cur==0:
    best=dict(y=y,c=c,E=sorted(E)); break
print(json.dumps(dict(t=t,n=n,N=N,q=q,found=best is not None,detail=best)))
