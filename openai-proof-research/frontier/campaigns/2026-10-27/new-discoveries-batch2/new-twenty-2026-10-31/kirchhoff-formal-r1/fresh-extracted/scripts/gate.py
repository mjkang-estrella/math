from pathlib import Path
from fractions import Fraction as Q
import json,hashlib,urllib.request,urllib.error,datetime
D=Path(__file__).resolve().parents[1]; n=11
E=[(i,j) for i in range(6) for j in range(i+1,6)]+[(0,6),(6,7),(7,8),(8,9),(9,10)]
d=[sum(i in e for e in E) for i in range(n)]
def eye():return [[Q(i==j) for j in range(n)] for i in range(n)]
def transpose(A):return list(map(list,zip(*A)))
def mul(A,B):return [[sum((A[i][k]*B[k][j] for k in range(n)),Q(0)) for j in range(n)] for i in range(n)]
def add(A,B,s=1):return [[A[i][j]+s*B[i][j] for j in range(n)] for i in range(n)]
def inv(A):
 B=[row[:]+r for row,r in zip(A,eye())]
 for k in range(n):
  t=next(t for t in range(k,n) if B[t][k]);B[t],B[k]=B[k],B[t];v=B[k][k];B[k]=[x/v for x in B[k]]
  for i in range(n):
   if i!=k:
    v=B[i][k];B[i]=[x-v*y for x,y in zip(B[i],B[k])]
 return [r[n:] for r in B]
def zero(A):return all(x==0 for r in A for x in r)
def index(A,source=True):return sum((A[i][i]+A[j][j]-A[i][j]-(A[j][i] if source else A[i][j]) for i in range(n) for j in range(i+1,n)),Q(0))
def run():
 seen={0}
 for _ in range(n):
  seen |= {v for u,v in E if u in seen} | {u for u,v in E if v in seen}
 assert len(seen)==n and len(E)==len(set(E)) and all(0<=u<v<n for u,v in E)
 assert d==[6,5,5,5,5,5,2,2,2,2,1]
 out={'edges':E,'degrees':d,'connected':True,'simple':True,'variants':{},'negative_controls':{}}
 for a in [-1,0,1]:
  C=[[Q(d[i],d[j])**a if (min(i,j),max(i,j)) in E else Q(0) for j in range(n)] for i in range(n)]
  L=[[(sum(C[i]) if i==j else -C[i][j]) for j in range(n)] for i in range(n)]
  w=[Q(x)**(-2*a) for x in d];P=[[w[j]/sum(w) for j in range(n)] for i in range(n)]
  G=add(inv(add(L,P)),P,-1)
  # Orthogonal right-null and left-null projectors; exact MP construction from group inverse.
  U=[[Q(1,n) for j in range(n)] for i in range(n)];W=[[w[i]*w[j]/sum(x*x for x in w) for j in range(n)] for i in range(n)]
  M=mul(mul(add(eye(),U,-1),G),add(eye(),W,-1))
  assert mul(mul(L,M),L)==L and mul(mul(M,L),M)==M
  assert transpose(mul(L,M))==mul(L,M) and transpose(mul(M,L))==mul(M,L)
  assert mul(mul(L,G),L)==L and mul(mul(G,L),G)==G and mul(L,G)==mul(G,L)
  assert mul(L,G)==add(eye(),P,-1)
  assert all(sum(r)==0 for r in L)
  assert all(sum(w[i]*L[i][j] for i in range(n))==0 for j in range(n))
  physical=[]
  for i in range(n):
   for j in range(i+1,n):
    if w[i]==w[j]:
     V=[G[k][i]-G[k][j] for k in range(n)]
     assert all(sum(L[k][t]*V[t] for t in range(n))==Q((k==i)-(k==j)) for k in range(n))
     physical.append({'pair':[i,j],'resistance':str(V[i]-V[j])})
  out['variants'][str(a)]={'L':L,'group_inverse':G,'mp_inverse':M,'spectral_index':n*sum(G[i][i] for i in range(n)),'source_mp_index':index(M),'assignment_mp_index':index(M,False),'source_group_pair_sum':index(G),'assignment_group_pair_sum':index(G,False),'physical_solvable_pairs':physical,'physical_full_index_defined':len(physical)==55,'left_null_obstruction_0_10':w[0]-w[10]}
  out['negative_controls'][str(a)]={'group_fails_penrose_symmetry':transpose(mul(L,G))!=mul(L,G),'mp_fails_commutation':mul(L,M)!=mul(M,L)}
  bad=[r[:] for r in M];bad[0][0]+=1
  assert mul(mul(L,bad),L)!=L
  out['negative_controls'][str(a)]['perturbed_mp_rejected']=True
 assert out['variants']['1']['source_mp_index']<out['variants']['0']['source_mp_index']
 assert out['variants']['1']['spectral_index']==Q(1696684,14035)
 assert out['variants']['0']['spectral_index']==Q(370,3)
 (D/'outputs/exact-independent.json').write_text(json.dumps(out,indent=2,default=str))
 print(json.dumps({a:{k:str(v) for k,v in r.items() if k.endswith('index') or k.endswith('sum') or k.startswith('left_null')} for a,r in out['variants'].items()},indent=2))
if __name__=='__main__':run()
