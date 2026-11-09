import pathlib,json
from fractions import Fraction as F
D=pathlib.Path(__file__).resolve().parents[1]
o=json.loads((D/'outputs/riordan-witness.json').read_text());a=[[F(x) for x in r] for r in o['A']];n=len(a);piv=[];k=0
for j in range(n):
 p=next((i for i in range(k,n) if a[i][j]),None)
 if p is None:continue
 a[k],a[p]=a[p],a[k];v=a[k][j];a[k]=[x/v for x in a[k]]
 for i in range(n):
  if i!=k:
   v=a[i][j];a[i]=[x-v*y for x,y in zip(a[i],a[k])]
 piv.append(j);k+=1
x=[F(0)]*n;x[next(i for i in range(n) if i not in piv)]=1
for i,j in enumerate(piv):x[j]=-sum(a[i][t]*x[t] for t in range(n) if t not in piv)
print(x);assert all(sum(v*y for v,y in zip(r,x))==0 for r in o['A']);o['kernel']=[str(y) for y in x]
(D/'outputs/riordan-witness.json').write_text(json.dumps(o,indent=2)+'\n')
