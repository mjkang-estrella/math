import itertools,json,time,sys
from pathlib import Path
D=Path(__file__).resolve().parents[1]
def graphs(n):
 es=list(itertools.combinations(range(n),2))
 for m in range(1<<len(es)):
  a=[0]*n
  for i,(u,v) in enumerate(es):
   if m>>i&1:a[u]|=1<<v;a[v]|=1<<u
  yield m,a
def subsets(n):return sorted(range(1<<n),key=int.bit_count)
def ind(a,s):return all(not(a[v]&s) for v in range(len(a)) if s>>v&1)
def iso(a,s):
 covered=s
 for v in range(len(a)):
  if s>>v&1:covered|=a[v]
 return ind(a,((1<<len(a))-1)^covered)
def iota(a):return next(s.bit_count() for s in subsets(len(a)) if iso(a,s))
def posvalid(a,mono):
 n=len(a);bad=set()
 if mono:
  def walk(path):
   vs=path
   for u in range(n):
    if u in vs or not(a[vs[-1]]>>u&1):continue
    if any(a[u]>>v&1 for v in vs[:-1]):continue
    q=vs+[u]
    for t in itertools.combinations(q,3):bad.add(sum(1<<v for v in t))
    walk(q)
  for v in range(n):walk([v])
 else:
  dist=[[n+1]*n for _ in a]
  for v in range(n):
   dist[v][v]=0;q=[v]
   for u in q:
    for w in range(n):
     if a[u]>>w&1 and dist[v][w]>n:dist[v][w]=dist[v][u]+1;q.append(w)
  for t in itertools.combinations(range(n),3):
   if any(dist[x][z]<=n and dist[x][z]==dist[x][y]+dist[y][z] for x,y,z in itertools.permutations(t)):bad.add(sum(1<<v for v in t))
 return [s for s in range(1,1<<n) if ind(a,s) and not any(t&s==t for t in bad)]
def chrom(n,valid):
 byv=[[] for _ in range(n)]
 for s in valid:
  for v in range(n):
   if s>>v&1:byv[v].append(s)
 dp=[0]*(1<<n)
 for s in range(1,1<<n):
  v=(s&-s).bit_length()-1;dp[s]=1+min(dp[s^t] for t in byv[v] if t&s==t)
 return dp[-1]
def ng(n):
 count=0;worst={k:(0,None) for k in ['gp','mp']}
 for m,a in graphs(n):
  comp=[((1<<n)-1)^(1<<v)^a[v] for v in range(n)]
  if tuple(a)>tuple(comp):continue
  for k in worst:
   z=chrom(n,posvalid(a,k=='mp'))+chrom(n,posvalid(comp,k=='mp'))
   if z>worst[k][0]:worst[k]=(z,m)
   if z>n+1: print('COUNTEREXAMPLE',n,m,k,z,flush=True)
  count+=1
 print(json.dumps(dict(n=n,count_complement_representatives=count,worst=worst)),flush=True)
if __name__=='__main__':
 for n in range(1,int(sys.argv[1])+1):ng(n)
