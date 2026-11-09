import json,itertools,sys,time,pathlib
lane=pathlib.Path(__file__).resolve().parents[1]
def edges(m,n):
 v=list(itertools.product(range(m),range(n)))
 return [(i,j) for i in range(len(v)) for j in range(i+1,len(v)) if (v[i][0]==v[j][0] and (v[i][1]-v[j][1])%n in (1,n-1)) or (v[i][1]==v[j][1] and (v[i][0]-v[j][0])%m in (1,m-1))]
def positive(E,M):
 # Theorem 1.1 pendant elimination, with fresh induced degrees each iteration.
 S=set(M)
 while S:
  V={v for e in S for v in e}; deg={v:0 for v in V}
  for a,b in E:
   if a in V and b in V: deg[a]+=1;deg[b]+=1
  e=next((e for e in S if min(deg[e[0]],deg[e[1]])==1),None)
  if e is None:return False
  S.remove(e)
 return True
if len(sys.argv)==1:
 c=json.loads((lane.parent/'expanded-corpus-r143/outputs/pmd-certificate.json').read_text()); E=set(edges(3,4)); assert len(E)==24
 residual=set(E); out=[]
 for k,(M,w) in enumerate(zip(c['layers'],c['weights'])):
  M={tuple(e) for e in M};assert M and M<=residual and len({v for e in M for v in e})==2*len(M)
  signs=[{'edge':e,'sum':w[e[0]]+w[e[1]],'selected':e in M} for e in sorted(residual)]
  assert all((s['sum']>0 if s['selected'] else s['sum']<0) for s in signs)
  assert positive(residual,M)
  out.append({'stage':k+1,'edges':signs});residual-=M
 assert not residual
 (lane/'logs/independent-signs.json').write_text(json.dumps(out,indent=2)+'\n')
 print('Independent adjacency, partition, matchings, strict signs, pendant positivity: PASS. Exact pmd = 5 using regular lower-bound argument in REVIEW.md.')
else:
 m,n=map(int,sys.argv[1:]); E0=tuple(edges(m,n)); N=m*n; start=time.monotonic(); states=0; checked=0; cache=set()
 def solve(E,k):
  global states,checked
  states+=1
  if time.monotonic()-start>22:raise TimeoutError
  if not E:return []
  if k==0:return None
  key=(E,k)
  if key in cache:return None
  deg=[0]*N
  for a,b in E:deg[a]+=1;deg[b]+=1
  if max(deg)>k or len(E)>k*(N//2):return None
  if k==1:return [list(E)] if max(deg)<=1 else None
  required={i for i,d in enumerate(deg) if d==k}
  candidates=[]
  def gen(i,used,M):
   if time.monotonic()-start>22:raise TimeoutError
   if i==len(E):
    if M and required<=used and positive(E,M):candidates.append(tuple(M))
    return
   a,b=E[i]
   if a not in used and b not in used:gen(i+1,used|{a,b},M+[(a,b)])
   gen(i+1,used,M)
  gen(0,set(),[])
  for M in sorted(candidates,key=len,reverse=True):
   checked+=1; s=set(M); rest=tuple(e for e in E if e not in s); r=solve(rest,k-1)
   if r is not None:return [list(M)]+r
  cache.add(key);return None
 try:
  r=solve(E0,5);print(json.dumps({'m':m,'n':n,'five_parts':r,'complete':True,'states':states,'candidates_tried':checked,'seconds':time.monotonic()-start}))
 except TimeoutError:print(json.dumps({'m':m,'n':n,'complete':False,'states':states,'candidates_tried':checked,'seconds':time.monotonic()-start}))
