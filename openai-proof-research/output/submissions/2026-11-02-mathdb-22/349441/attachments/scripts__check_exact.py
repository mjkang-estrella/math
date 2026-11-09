from pathlib import Path
from fractions import Fraction as F
import json,hashlib
D=Path(__file__).resolve().parents[1]
f=D/'sources/kirchhoff-review-r1/outputs/witness-exact.json';data=json.loads(f.read_text())
n=11
I=[[F(i==j) for j in range(n)] for i in range(n)]
def mul(A,B):return [[sum(A[i][k]*B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
def tr(A):return [[A[j][i] for j in range(n)] for i in range(n)]
deg=[6]+[5]*5+[2]*4+[1]
edges={(i,j) for i in range(6) for j in range(i+1,6)}|{(0,6),(6,7),(7,8),(8,9),(9,10)}
results={}
for alpha,row in data.items():
 a=int(alpha);mpval,specval,mat=row
 A,M,G=[[[F(x) for x in r] for r in mat[k]] for k in ['L','MP','GI']]
 L=[[F(0) for j in range(n)] for i in range(n)]
 for i,j in edges:
  for u,v in [(i,j),(j,i)]:L[u][v]=-F(deg[u],deg[v])**a;L[u][u]-=L[u][v]
 assert A==L
 AM,MA=mul(A,M),mul(M,A)
 assert mul(AM,A)==A and mul(MA,M)==M and tr(AM)==AM and tr(MA)==MA
 AG,GA=mul(A,G),mul(G,A)
 assert mul(AG,A)==A and mul(GA,G)==G and AG==GA
 pair=sum(M[i][i]+M[j][j]-M[i][j]-M[j][i] for i in range(n) for j in range(i+1,n))
 spec=n*sum(G[i][i] for i in range(n))
 assert pair==F(mpval) and spec==F(specval)
 results[alpha]={'MP':str(pair),'spectral':str(spec),'equations':'PASS'}
assert F(370,3)-F(1696684,14035)==F(102898,42105)>0
(D/'receipts/exact-cross-check.json').write_text(json.dumps({'status':'PASS','source_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'values':results},indent=2)+'\n')
print('Exact cross-check PASS')
