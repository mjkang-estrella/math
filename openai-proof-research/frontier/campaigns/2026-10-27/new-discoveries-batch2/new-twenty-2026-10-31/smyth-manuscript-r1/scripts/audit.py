"""Fresh audit from finite maps, rearrangement and prefix sums. Standard library only."""
import json,hashlib,sys,math
from pathlib import Path
from collections import Counter,deque
from functools import lru_cache
R=Path(__file__).resolve().parent.parent
@lru_cache(None)
def comps(m,n):
 if not m:return ((),) if n==0 else ()
 return tuple((i,)+t for i in range(n+1) for t in comps(m-1,n-i))
def rearr(p):return tuple(sorted(p,reverse=True))
def dom(p,q):
 if sum(p)!=sum(q):return False
 x=y=0
 for i in range(max(len(p),len(q))):
  x+=p[i] if i<len(p) else 0;y+=q[i] if i<len(q) else 0
  if x<y:return False
 return True
def parts(n,m,top=None):
 if not m:
  if not n:yield ()
  return
 for i in range(min(n,n if top is None else top),-1,-1):
  if i*m<n:break
  for t in parts(n-i,m-1,i):yield(i,)+t
def multiplicity(p,A,b):
 # For each value choose how many copies occupy the first A positions.
 counts=Counter(p); dp={(0,0):1}; den=1
 for v,c in counts.items():
  den*=math.factorial(c);nd={}
  for (k,s),w in dp.items():
   for j in range(min(c,A-k)+1):
    if s+j*v<=b:nd[k+j,s+j*v]=nd.get((k+j,s+j*v),0)+w*math.comb(c,j)
  dp=nd
 return dp.get((A,b),0)*math.factorial(A)*math.factorial(len(p)-A)//den
class Flow:
 def __init__(self,n):self.g=[[] for _ in range(n)]
 def add(self,u,v,c):
  self.g[u].append([v,c,len(self.g[v])]);self.g[v].append([u,0,len(self.g[u])-1])
 def run(self):
  out=0
  while True:
   lv=[-1]*len(self.g);lv[0]=0;q=deque([0])
   while q:
    u=q.popleft()
    for v,c,r in self.g[u]:
     if c and lv[v]<0:lv[v]=lv[u]+1;q.append(v)
   if lv[1]<0:return out
   it=[0]*len(self.g)
   def dfs(u,f):
    if u==1:return f
    while it[u]<len(self.g[u]):
     e=self.g[u][it[u]];v,c,r=e
     if c and lv[v]==lv[u]+1:
      d=dfs(v,min(c,f))
      if d:e[1]-=d;self.g[v][r][1]+=d;return d
     it[u]+=1
    return 0
   while True:
    d=dfs(0,10**12)
    if not d:break
    out+=d
def network(A,a,B,b,reverse=False):
 P=list(parts(a+b,A+B));ix={p:i+2 for i,p in enumerate(P)};f=Flow(len(P)+2);nx=ny=0
 for p in P:
  x=multiplicity(p,A,b);y=multiplicity(p,A,a);nx+=x;ny+=y
  if x:f.add(0,ix[p],x)
  if y:f.add(ix[p],1,y)
  moves=set()
  for i in range(len(p)):
   for j in range(len(p)):
    if p[i]>=p[j]+2:
     q=list(p);q[i]-=1;q[j]+=1;moves.add(rearr(q))
  for q in moves:
   assert dom(p,q)
   f.add(ix[q] if reverse else ix[p],ix[p] if reverse else ix[q],10**12)
 return nx,ny,f.run()
def certificate():
 G=[(13,12,8,4,2),(13,13,7,3,3),(12,12,8,6,1),(14,12,6,4,3),(13,11,7,7,1),(14,11,6,6,2),(15,11,5,5,3),(16,10,5,4,4)]
 assert len(G)==8 and all(sum(g)==39 and rearr(g)==g for g in G)
 X=[(u,v) for u in comps(3,19) for v in comps(2,20)];Y=[(u,v) for u in comps(3,20) for v in comps(2,19)]
 D={p for p in parts(39,5) if any(dom(g,p) for g in G)}
 out={'parameters':[3,20,2,19],'generators':G,'composition_counts':[len(comps(m,n)) for m,n in [(3,19),(2,20),(3,20),(2,19)]],'X':len(X),'Y':len(Y),'D_five_part':len(D),'rows':{},'hashes':{}}
 for name,L in [('S',[x for x in X if rearr(x[0]+x[1]) in D]),('T',[y for y in Y if rearr(y[0]+y[1]) in D])]:
  b=19 if name=='S' else 20
  out[name]=len(L);out['rows'][name]=[sum(u[0]==i for u,v in L) for i in range(b+1)]
  data=json.dumps(sorted(L)).encode();(R/(name+'.json')).write_bytes(data);out['hashes'][name]=hashlib.sha256(data).hexdigest()
 assert (out['S'],out['T'])==(1137,1134)
 # Verify multiplicity independently against literal element enumeration.
 for L,A,b in [(X,3,19),(Y,3,20)]:
  C=Counter(rearr(u+v) for u,v in L)
  assert all(multiplicity(p,A,b)==C[p] for p in parts(39,5))
 out['type_flow']=network(3,20,2,19);out['reversed_flow']=network(3,20,2,19,True)
 (R/'audit-certificate.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
def family(b):
 out={'b':b,'result':network(3,b+1,2,b)}
 assert out['result'][2]<out['result'][0]
 (R/f'audit-family-{b}.json').write_text(json.dumps(out)+'\n');print(out,flush=True)
def sweep(A,B):
 cases=[]
 for a in range(11):
  for b in range(a):
   if a+b<=16:
    nx,ny,f=network(A,a,B,b);assert f==nx;(cases.append([A,a,B,b,nx,ny,f]))
 (R/f'audit-sweep-{A}-{B}.json').write_text(json.dumps(cases)+'\n');print(A,B,len(cases),'pass',flush=True)
if __name__=='__main__':
 sys.setrecursionlimit(20000)
 if sys.argv[1]=='certificate':certificate()
 elif sys.argv[1]=='family':family(int(sys.argv[2]))
 elif sys.argv[1]=='sweep':sweep(*map(int,sys.argv[2:]))
