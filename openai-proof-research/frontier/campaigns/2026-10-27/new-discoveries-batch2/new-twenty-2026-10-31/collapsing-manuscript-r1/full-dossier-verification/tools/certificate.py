import ast,re,json
from pathlib import Path
from fractions import Fraction as Q
D=Path(__file__).resolve().parents[1]
s=(D/'proof/MathDB378395.lean').read_text()
block=s.split('def bcell :')[1].split('theorem ell_basis')[0]
cells=ast.literal_eval(block[block.index('![')+1:].strip())
def col(c):
 i,j,k=c;v=[0]*56;v[4*i+j]=v[16+5*i+k]=v[36+5*j+k]=1;return v
# select independent coordinate rows, then Bareiss certificate
rows=[[col(c)[i] for c in cells] for i in range(56)]
M=[list(map(Q,r)) for r in rows];ids=list(range(56));piv=[]
for k in range(43):
 t=next(i for i in range(k,56) if M[i][k]);M[k],M[t]=M[t],M[k];ids[k],ids[t]=ids[t],ids[k];piv.append(ids[k])
 for i in range(k+1,56):
  f=M[i][k]/M[k][k];M[i]=[a-f*b for a,b in zip(M[i],M[k])]
N=[[rows[i][j] for j in range(43)] for i in piv];last=1;diagonal=[]
for k in range(42):
 p=N[k][k];assert p
 diagonal.append(p)
 for i in range(k+1,43):
  for j in range(k+1,43):
   x=N[i][j]*p-N[i][k]*N[k][j];assert x%last==0;N[i][j]=x//last
  N[i][k]=0
 last=p
diagonal.append(N[-1][-1]);assert abs(diagonal[-1])==1
r={'cells':cells,'coordinate_rows':piv,'bareiss_pivots':diagonal,'determinant':diagonal[-1],'convention':'12 row-major 0..15; 13 16..35; 23 36..55; ordered rows as listed; no row swaps in Bareiss'}
(D/'receipts/minor-certificate.json').write_text(json.dumps(r,indent=2));print(r)
