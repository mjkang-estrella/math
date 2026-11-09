import itertools as it, json, pathlib, math,time,sys
from fractions import Fraction as F
D=pathlib.Path(__file__).resolve().parents[1]
def out(k,v):
 (D/f'outputs/search-{k}.json').write_text(json.dumps(v,indent=2)+'\n');print(k,v,flush=True)
def graphs():
 rows=[]
 def cycle(a,length):
  n=len(a)
  def go(path):
   if len(path)==length:return path[0] in a[path[-1]]
   return any(go(path+[v]) for v in a[path[-1]] if v>path[0] and v not in path)
  return any(go([v]) for v in range(n))
 def factors(n,es):
  if not es:return True
  def pm(vs,chosen):
   if not vs:return factors(n,es-set(chosen))
   v=min(vs)
   return any(pm(vs-{v,w},chosen+[(min(v,w),max(v,w))]) for w in vs-{v} if (min(v,w),max(v,w)) in es)
  return pm(set(range(n)),[])
 for n in range(1,7):
  edges=list(it.combinations(range(n),2));cnt=[0,0,0]
  for mask in range(1<<len(edges)):
   es={e for k,e in enumerate(edges) if mask>>k&1};a=[set() for _ in range(n)]
   for u,v in es:a[u].add(v);a[v].add(u)
   deg=list(map(len,a))
   if min(deg)>=3:
    cnt[0]+=1;assert any(cycle(a,l) for l in [4,8] if l<=n)
   if n%2==0 and len(set(deg))==1 and deg[0]>=n//2-(n//2%2==0):cnt[1]+=1;assert factors(n,es)
   if n>=5 and min(deg)>=4:
    connected=True
    for m in range(4):
     for removed in it.combinations(range(n),m):
      rem=set(range(n))-set(removed);seen={min(rem)};todo=list(seen)
      while todo:
       for v in a[todo.pop()]&rem-seen:seen.add(v);todo.append(v)
      if seen!=rem:connected=False;break
     if not connected:break
    if connected:cnt[2]+=1;assert cycle(a,n)
  rows.append(dict(n=n,graphs=1<<len(edges),min_degree3=cnt[0],factorization_applicable=cnt[1],four_connected=cnt[2]))
 out('graphs',dict(ids=[315995,316020,316022],space='all labeled simple graphs orders 1..6; for 316022 Hamiltonicity checked on all 4-connected graphs, toroidal hypothesis unnecessary in this bounded range',rows=rows,counterexamples=[]))
def union():
 rows=[]
 for n in range(4,5):
  for s in range(4,5):
   pts=[a for a in it.product(range(s+1),repeat=n) if sum(a)<=s]
   for r in range(2,min(n+1,4)):
    if n-r+1<=0:continue
    Ks=[]
    for d in range(s//r+1):
     w=s-r*d;base=tuple([w//n+1]*(w%n)+[w//n]*(n-w%n));fam=set()
     for a in set(it.permutations(base)):
      K={x for x in pts if any(sum(max(0,x[j]-a[j]-i) for j in range(n))<=d-(n-r+1)*i for i in range(d//(n-r+1)+1))};Ks.append(K)
    bound=max(map(len,Ks));nodes=0;best=0;bad=[];ties=0;cap=2000
    def dfs(chosen,candidates):
     nonlocal nodes,best,ties
     nodes+=1
     if nodes>cap:raise TimeoutError
     best=max(best,len(chosen))
     if len(chosen)>=bound:
      fam={pts[k] for k in chosen}
      if len(chosen)>bound or fam not in Ks:bad.append(sorted(fam))
      ties+=1
     for j,k in enumerate(candidates):
      if all(sum(max(pts[t][h] for t in tup) for h in range(n))<=s for tup in it.combinations_with_replacement(chosen+[k],r) if k in tup):dfs(chosen+[k],candidates[j+1:])
    complete=True
    try:dfs([],list(range(len(pts))))
    except TimeoutError:complete=False
    rows.append(dict(n=n,s=s,r=r,points=len(pts),nodes=nodes,complete=complete,bound=bound,best=best,ties=ties,counterexamples=bad[:2]))
 out('union-deep',dict(id=331759,space='all families of nonnegative vectors with weight <=s, lexicographic include recursion, cap2000 nodes per parameter',rows=rows))
def paths():
 rows=[]
 for n in range(1,10):
  def gen(x,y,w):
   if x==y==n:return int(w.endswith('E'))
   z=0
   if x<n and y>x and not w.endswith('N'):z+=gen(x+1,y,w+'E')
   if y<n and not w.endswith('E'):z+=gen(x,y+1,w+'N')
   if x<n and y<n:z+=gen(x+1,y+1,w+'D')
   return z
  def dyck(u,d,runs):
   if u==d==n+1:return int(all(runs[i]!=runs[i+1] for i in range(0,len(runs)-1,2)))
   return sum(dyck(u+(c=='N'),d+(c=='E'),runs[:-1]+[runs[-1]+1] if (len(runs)%2==1)==(c=='N') else runs+[1]) for c in ['N','E'] if (c=='N' and u<n+1) or (c=='E' and d<u))
  a=gen(0,0,'');b=dyck(0,0,[]);rows.append([n,a,b]);assert a==b
 out('paths',dict(id=381659,space='all admissible Delannoy words and all Dyck words semilength n+1 for n1..9; symmetric peaks use equal adjacent maximal up/down run lengths',rows=rows))
def powers():
 rows=[]
 for k in range(3,9):
  N=15; sums={};tests=0;bad=[]
  for m in range(1,k//2+1):
   for n in range(m,k-m):
    if n>3:continue
    left={}
    for a in it.combinations_with_replacement(range(1,N+1),m):left.setdefault(sum(x**k for x in a),[]).append(a)
    for b in it.combinations_with_replacement(range(1,N+1),n):
     tests+=1
     for a in left.get(sum(x**k for x in b),[]):
      if not set(a)&set(b):bad.append([a,b])
  rows.append(dict(k=k,max_entry=N,max_side_length=3,tests=tests,counterexamples=bad))
 out('powers',dict(id=316062,rows=rows))
if __name__=='__main__':globals()[sys.argv[1]]()
