"""Bounded arithmetic checks only; no external dependencies or file writes."""
from itertools import permutations, product
import json
Z=(0,0,0,0); ONE=(1,0,0,0)
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def scale(a,k):return tuple(k*x for x in a)
def mul(a,b):
 c=[0]*7
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 for k in range(6,3,-1):c[k-2]+=c[k];c[k-4]-=c[k]
 return tuple(c[:4])
def zp(k):
 a=ONE
 for _ in range(k%12):a=mul(a,(0,1,0,0))
 return a
def parity(p):return sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))%2
def determinant(M):
 n=len(M);res=Z
 for p in permutations(range(n)):
  a=ONE
  for i,j in enumerate(p):
   if M[i][j]==Z:break
   a=mul(a,M[i][j])
  else:res=add(res,scale(a,(-1)**parity(p)))
 return res
def sign_solution(states,n):
 # Solve sign equations on the eligible incidence edges (bounded test only).
 edges=sorted({(t,s[t]) for s in states for t in range(n)})
 ix={e:i for i,e in enumerate(edges)};basis={}
 for s in states:
  mask=sum(1<<ix[t,s[t]] for t in range(n));rhs=parity(s)
  while mask:
   k=mask.bit_length()-1
   if k in basis:mask^=basis[k][0];rhs^=basis[k][1]
   else:basis[k]=(mask,rhs);break
  else:assert rhs==0
 sol=0
 for k,(mask,rhs) in sorted(basis.items()):
  if (sol&mask).bit_count()%2!=rhs:sol|=1<<k
 return {e:(-1)**((sol>>i)&1) for e,i in ix.items()}
def spoke_weights(rim, faces):
 # Build the source inherited rotation system using its actual white faces.
 from collections import deque
 apex=rim;bottom=rim+1;blacks=[(apex,0,1)]+faces
 centers=[rim+2+i for i in range(len(blacks))];outer_center=centers[0]
 owner={tuple(sorted((f[i],f[(i+1)%3]))):centers[t] for t,f in enumerate(blacks) for i in range(3)}
 whites=[(apex,i,(i+1)%rim) for i in range(1,rim,2)]+[(bottom,(i+1)%rim,i) for i in range(0,rim,2)]
 nxt={}
 for f in whites:
  boundary=[]
  for i,v in enumerate(f):boundary.extend([v,owner[tuple(sorted((v,f[(i+1)%3])))]] )
  edges=[(boundary[i],boundary[(i+1)%6]) for i in range(6)]
  for i,e in enumerate(edges):assert e not in nxt;nxt[e]=edges[(i+1)%6]
 live={e for e in nxt if outer_center not in e};nxt0={};touched=set()
 for e in live:
  f=nxt[e]
  while outer_center in f:touched.add(e);f=nxt[f[1],f[0]]
  nxt0[e]=f
 fs=[];seen=set()
 for start in sorted(live):
  if start in seen:continue
  face=[];e=start
  while e not in seen:seen.add(e);face.append(e);e=nxt0[e]
  assert e==start;fs.append(face)
 outer=[i for i,f in enumerate(fs) if any(e in touched for e in f)];assert len(outer)==1;outer=outer[0]
 ef={e:i for i,f in enumerate(fs) for e in f};dual={i:[] for i in range(len(fs))}
 for e,i in ef.items():
  j=ef[e[1],e[0]]
  if i!=j:dual[i].append((j,e))
 a={tuple(sorted(e)):0 for e in live}
 for start in range(len(fs)):
  if start==outer:continue
  todo=deque([start]);parent={start:None}
  while outer not in parent:
   v=todo.popleft()
   for w,e in dual[v]:
    if w not in parent:parent[w]=(v,e);todo.append(w)
  v=outer
  while v!=start:
   u,e=parent[v]
   # e is traversed along the departing face, giving +1 to it.
   a[tuple(sorted(e))]+=1 if e[0] in centers else -1
   v=u
 B=len(fs)-1
 for i,f in enumerate(fs):
  circulation=sum(a[tuple(sorted(e))]*(1 if e[0] in centers else -1) for e in f)
  assert circulation==(1 if i!=outer else -B)
 assert B==len(faces)-2 and max(map(abs,a.values()))<=B
 return B,{(t,v):a[tuple(sorted((centers[t+1],v)))]+B for t,f in enumerate(faces) for v in f}
def instance(rim):
 apex=rim;bottom=rim+1
 faces=[(apex,i,(i+1)%rim) for i in range(2,rim,2)]+[(bottom,(i+1)%rim,i) for i in range(1,rim,2)]
 X=[i for i in range(rim+2) if i not in (apex,0,1)];n=len(X);idx={v:i for i,v in enumerate(X)}
 loc=[{idx[v]:k for k,v in enumerate(f) if v in idx} for f in faces]
 states=[p for p in permutations(range(n)) if all(p[t] in loc[t] for t in range(n))]
 pairs=[(r,s) for r in states for s in states if all(a!=b for a,b in zip(r,s))]
 kap=sign_solution(states,n)
 B,incidence_weights=spoke_weights(rim,faces)
 weight=lambda t,j:incidence_weights[t,X[j]]
 for r,s in pairs:
  J=sum(1 if (loc[t][s[t]]-loc[t][r[t]])%3==1 else -1 for t in range(n))//3
  diff=sum(weight(t,s[t])-weight(t,r[t]) for t in range(n))
  assert -J*diff>0
 phase=lambda t,a,b:zp(1 if (loc[t][b]-loc[t][a])%3==1 else -1)
 results=[]
 restrictions=[{}, {0:states[0][0]}, {0:states[0][0],1:states[-1][1]}]
 for j in [2,3]:
  for sigma in restrictions:
   direct=Z
   for r,s in pairs:
    if any(s[t]!=v for t,v in sigma.items()):continue
    a=ONE
    for t in range(n):a=mul(a,phase(t,r[t],s[t]))
    direct=add(direct,scale(a,j**sum(weight(t,s[t]) for t in range(n))))
   if rim<=6:
    total=Z
    U=[(ONE,Z),(Z,ONE),(zp(-2),zp(2))]
    V=[(Z,zp(-1)),(zp(1),Z),(zp(-1),zp(1))]
    for eps in product([0,1],repeat=n):
     R=[[scale(U[loc[t][v]][eps[t]],kap[t,v]) if v in loc[t] else Z for v in range(n)] for t in range(n)]
     S=[[scale(V[loc[t][v]][eps[t]],kap[t,v]*j**weight(t,v)) if v in loc[t] and (t not in sigma or sigma[t]==v) else Z for v in range(n)] for t in range(n)]
     total=add(total,mul(determinant(R),determinant(S)))
    assert total==direct
   results.append({'j':j,'sigma':sigma,'direct':direct,'rank_two_checked':rim<=6})
 # Stronger direct single-determinant attempt, all face variables set to one.
 j=2;M=[[Z]*n for _ in range(n)];owner={}
 for t,L in enumerate(loc):
  for a in L:
   for b in L:
    if a==b:continue
    assert (a,b) not in owner
    owner[a,b]=t
    M[a][b]=scale(zp(-1 if (L[b]-L[a])%3==1 else 1),j**weight(t,b))
 full=determinant(M);sqfree=Z;repeated=Z;poly_square={};poly_repeated={}
 for p in permutations(range(n)):
  if any((v,p[v]) not in owner for v in range(n)):continue
  a=ONE;counts=[0]*n;phase_product=ONE;degree=0
  for v in range(n):
   t=owner[v,p[v]];a=mul(a,M[v][p[v]]);counts[t]+=1;degree+=weight(t,p[v])
   phase_product=mul(phase_product,zp(-1 if (loc[t][p[v]]-loc[t][v])%3==1 else 1))
  bucket=poly_square if counts==[1]*n else poly_repeated
  bucket[degree]=add(bucket.get(degree,Z),scale(phase_product,(-1)**parity(p)))
  a=scale(a,(-1)**parity(p))
  if counts==[1]*n:sqfree=add(sqfree,a)
  else:repeated=add(repeated,a)
 assert scale(sqfree,(-1)**n)==tuple(results[0]['direct'])
 assert add(sqfree,repeated)==full
 inclusion=Z
 for subset in range(1<<n):
  masked=[[M[a][b] if (a,b) in owner and (subset>>owner[a,b])&1 else Z for b in range(n)] for a in range(n)]
  inclusion=add(inclusion,scale(determinant(masked),(-1)**(n-subset.bit_count())))
 assert inclusion==sqfree
 return dict(rim=rim,m=n,bounded_faces=B,shifted_weights={str(k):v for k,v in incidence_weights.items()},states=len(states),pairs=len(pairs),cases=results,single_det=full,squarefree=sqfree,inclusion_exclusion=inclusion,repeated_face_remainder=repeated,squarefree_polynomial={k:v for k,v in poly_square.items() if v!=Z},repeated_polynomial={k:v for k,v in poly_repeated.items() if v!=Z})
if __name__=='__main__':
 out={'arithmetic':'Z[zeta]/(zeta^4-zeta^2+1), integer coordinates','instances':[instance(m) for m in [4,6,8]]}
 # Independent tiny Hamiltonian DFS; cube vertices are binary strings as integers.
 adj={v:[v^(1<<k) for k in range(3)] for v in range(8)};cycles=[]
 def dfs(path):
  if len(path)==8:
   if 0 in adj[path[-1]] and path[1]<path[-1]:cycles.append(path[:])
   return
  for v in adj[path[-1]]:
   if v not in path:dfs(path+[v])
 dfs([0]);required={tuple(sorted(e)) for e in zip([4,6,2,3],[6,2,3,1])}
 containing=[c for c in cycles if required<={tuple(sorted((c[i],c[(i+1)%8]))) for i in range(8)}]
 assert len(cycles)==6 and not containing
 out['cube']={'Hamiltonian_cycles':len(cycles),'cycles_containing_displayed_four_edge_path':len(containing)}
 print(json.dumps(out,indent=2))
