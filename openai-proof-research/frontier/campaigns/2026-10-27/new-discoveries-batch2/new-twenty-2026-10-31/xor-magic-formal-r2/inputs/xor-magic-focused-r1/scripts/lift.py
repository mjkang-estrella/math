import sys,json,itertools,random
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
from verify import verify,complement
# F4 = F2[z]/(z^2+z+1), integers 0..3.
def mul(a,b):
 t=0
 for i in range(2):
  if b>>i&1:t^=a<<i
 if t&4:t^=7
 return t
def inv(a):return {1:1,2:3,3:2}[a]
def cycles(F):
 a={}
 for u,v in F:a.setdefault(u,[]).append(v);a.setdefault(v,[]).append(u)
 assert all(len(v)==2 for v in a.values());seen=set();out=[]
 for s in a:
  if s in seen:continue
  c=[];u=s;prev=None
  while u not in seen:c.append(u);seen.add(u);v=next(v for v in a[u] if v!=prev);prev,u=u,v
  assert u==s;out.append(c)
 return out
def nullbasis(A):
 A=[r[:] for r in A];m=len(A);n=len(A[0]);piv=[];r=0
 for j in range(n):
  i=next((i for i in range(r,m) if A[i][j]),None)
  if i is None:continue
  A[r],A[i]=A[i],A[r];f=inv(A[r][j]);A[r]=[mul(f,x) for x in A[r]]
  for i in range(m):
   if i!=r and A[i][j]:
    f=A[i][j];A[i]=[x^mul(f,y) for x,y in zip(A[i],A[r])]
  piv.append(j);r+=1
  if r==m:break
 basis=[]
 for j in set(range(n))-set(piv):
  x=[0]*n;x[j]=1
  for i,k in enumerate(piv):x[k]=A[i][j]
  basis.append(x)
 return basis
rng=random.Random(372205)
def lift(g,F,C):
 N=g['N'];d=g['d'];cs=cycles(F[0]+F[1]);assert any(len(c)%3 for c in cs)
 twists={}
 for c in cs:
  for u,v in zip(c,c[1:]+c[:1]):twists[tuple(sorted((u,v)))]=2 if u<v else 3
 E=sorted(map(tuple,g['edges']));a=[twists.get(e,1) for e in E];B=[[0]*len(E) for _ in range(N)]
 for j,(u,v) in enumerate(E):B[u][j]=1;B[v][j]=inv(a[j])
 basis=nullbasis(B)
 def build(c):
  mapping={};edges=[]
  for j,(u,v) in enumerate(E):
   block=[(4*u+x,4*v+(mul(a[j],x)^c[j])) for x in range(4)];mapping[u,v]=block;edges+=block
  return dict(N=4*N,d=d,closed=g['closed'],edges=sorted(edges)),mapping
 def has_section(c):
  adj=[[] for _ in range(N)]
  for j,(u,v) in enumerate(E):adj[u].append((v,a[j],c[j]));adj[v].append((u,inv(a[j]),mul(inv(a[j]),c[j])))
  for root in range(4):
   vals={0:root};todo=[0];consistent=True
   for u in todo:
    for v,aa,cc in adj[u]:
     val=mul(aa,vals[u])^cc
     if v in vals:
      if vals[v]!=val:consistent=False
     else:vals[v]=val;todo.append(v)
   if consistent:return True
  return False
 for trial,c in enumerate(basis):
  if not has_section(c):break
 else:raise AssertionError('dimension argument violated')
 h,mp=build(c);verify(h)
 LF=[[e for uv in factor for e in mp[tuple(uv)]] for factor in F]
 # Complement factors: K4 per fibre; 3 matchings per base G factor;
 # 4 matchings per base complement factor. Each K44 minus matching is
 # split using output-coordinate translation by 1,2,3.
 LC=[]
 for t in [1,2,3]:LC.append([(4*u+x,4*u+(x^t)) for u in range(N) for x in range(4) if x<(x^t)])
 for factor in F:
  for t in [1,2,3]:LC.append([(x,y^t) for uv in factor for x,y in mp[tuple(uv)]])
 for factor in C:
  for t in range(4):LC.append([(4*u+x,4*v+(x^t)) for u,v in factor for x in range(4)])
 for factors,target in [(LF,h),(LC,complement(h))]:
  assert all(len(f)==2*N and len({u for e in f for u in e})==4*N for f in factors)
  assert sorted(e for f in factors for e in f)==target['edges']
 assert any(len(c)%3 for c in cycles(LF[0]+LF[1]))
 return h,LF,LC,dict(basis_vectors_tested=trial+1,base_N=N,base_d=d,nullity_F4=len(basis),cycles=[len(c) for c in cs],translations=c,edge_multipliers=a)
if __name__=='__main__':
 specs=[('outputs/base-16-4-1.json','outputs/base-16-4-1'),('../expanded-corpus-r90/outputs/xor-16-5.json','outputs/xor-16-5'),('outputs/seed-32-4-1.json','outputs/seed-32-4-1'),('outputs/seed-32-5-0.json','outputs/seed-32-5-0')];report=[]
 for path,prefix in specs:
  g=json.loads(Path(path).read_text());g.setdefault('closed',False);F=json.loads(Path(prefix+'-factors-0.json').read_text())['factors'];C=json.loads(Path(prefix+'-factors-1.json').read_text())['factors'];F=[[tuple(e) for e in f] for f in F];C=[[tuple(e) for e in f] for f in C];verify(g)
  for step in range(2):
   h,LF,LC,r=lift(g,F,C);report.append(r);Path(f'outputs/lift-{h["N"]}-{h["d"]}.json').write_text(json.dumps(h));
   if step==0:
    for k in range(len(F)+1):
     for j in range(len(C)+1):
      ed=set(map(tuple,h['edges']))
      for factor,lf in zip(F[:k],LF[:k]):
       ed-=set(lf)
       for u,v in factor:ed|={(4*u+x,4*v+y) for x in range(4) for y in range(4)}-set(lf)
      for factor in C[:j]:
       for u,v in factor:ed|={(4*u+x,4*v+y) for x in range(4) for y in range(4)}
      z=dict(N=h['N'],d=h['d']+2*k+4*j,closed=h['closed'],edges=sorted(ed));verify(z)
      if z['d']<z['N']//2:verify(complement(z))
    r['all_k_j_variants_verified']=True
   g,F,C=h,LF,LC
 Path('outputs/lift-verification.json').write_text(json.dumps(report,indent=2));print(report)
