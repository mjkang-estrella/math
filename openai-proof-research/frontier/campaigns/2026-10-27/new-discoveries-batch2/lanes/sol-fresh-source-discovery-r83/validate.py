from pathlib import Path
from itertools import permutations,product
import json
P=Path(__file__).resolve().parent

def indices(C):
 n=len(C);t=list(map(sum,C));T1=sum(t);T2=sum(x*x for x in t);Q=sum(t[i]*t[j] for i in range(n) for j in range(n) if C[i][j])
 out=[]
 for comp in [False,True]:
  A=[[int((not C[i][j]) if comp else (i!=j and C[i][j])) for j in range(n)]for i in range(n)]
  d=list(map(sum,A));S1=sum(d);S2=sum(x*x for x in d);E2=sum(d[i]*d[j] for i in range(n) for j in range(n) if A[i][j]);gap=n*E2-S1*S2
  predicted=(n*n+T1)*T2-n*T1*T1-n*Q if comp else n*Q-(T1+2*n)*T2+2*T1*T1
  assert gap==predicted
  out.append({'complement':comp,'n':n,'edges':S1//2,'M1':S2,'M2':E2//2,'twice_HV_gap':gap})
 return out
# actual S4, exact permutation products, no floating arithmetic
els=list(permutations(range(4)))
def mul(a,b):return tuple(a[b[i]] for i in range(4))
non=[a for a in els if any(mul(a,b)!=mul(b,a) for b in els)]
C=[[int(mul(a,b)==mul(b,a)) for b in non]for a in non]
s4=indices(C)
a=(1,0,2,3);b=(1,0,3,2);c=(2,3,1,0)
assert mul(c,c)==b
ids=[non.index(x) for x in [a,b,c]];minor=[[C[i][j] for j in ids]for i in ids];assert minor==[[1,1,0],[1,1,1],[0,1,1]]
v=[1,-1,1];assert sum(v[i]*minor[i][j]*v[j]for i in range(3)for j in range(3))==-1
# source's classical nongroup graph K1,5 disjoint K3
K=[[int(i==j or (i==0 and 1<=j<=5)or(j==0 and 1<=i<=5)or(i>=6 and j>=6))for j in range(9)]for i in range(9)]
classical=indices(K);assert classical[0]['twice_HV_gap']<0
# literal upper triangular central extension over F2; compressed vs full group graph
D=4;R=2;coeff=[1,2,1,1,3,2];pairs=[(i,j)for i in range(D)for j in range(i+1,D)]
def f(v,w):
 z=0
 for (i,j),c in zip(pairs,coeff):
  if (v>>i)&1 and (w>>j)&1:z^=c
 return z
def comm(v,w):return f(v,w)^f(w,v)
rad=[v for v in range(16)if all(comm(v,w)==0 for w in range(16))];assert rad==[0]
def gm(a,b):return(a[0]^b[0],a[1]^b[1]^f(a[0],b[0]))
G=list(product(range(16),range(4)))
# exhaustive cocycle check proves sampled implementation's associativity, not an all-group theorem
for v,w,u in product(range(16),repeat=3):assert f(v,w)^f(v^w,u)==f(w,u)^f(v,w^u)
N=[x for x in G if x[0]];full=[[int(gm(a,b)==gm(b,a))for b in N]for a in N];literal=indices(full)
A=[[int(comm(v,w)==0)for w in range(1,16)]for v in range(1,16)];k=list(map(sum,A));z=4;n=60;d=[z*t-1 for t in k]
M1=z*sum(x*x for x in d);twoM2=z*z*sum(d[i]*d[j]for i in range(15)for j in range(15)if A[i][j])-M1
assert M1==literal[0]['M1']and twoM2==2*literal[0]['M2']
print(json.dumps({'status':'PASS','S4':s4,'PSD_route_falsifier':{'minor':minor,'vector':v if False else [1,-1,1],'quadratic':-1},'classical_not_group_counterexample':classical,'literal_group_order':64,'literal_graph':literal,'cocycle_triples':4096,'scope':'Exact identities and method diagnostics only; no resolution.'},indent=2))
