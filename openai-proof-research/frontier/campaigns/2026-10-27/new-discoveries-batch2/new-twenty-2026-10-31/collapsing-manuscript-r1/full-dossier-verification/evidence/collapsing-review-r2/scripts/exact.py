from fractions import Fraction as Q
from itertools import product,combinations
import json,pathlib
R=pathlib.Path(__file__).resolve().parents[1]
a=[[0,0,0,0],[0,0,0,1],[0,0,1,1],[0,1,1,0]]
b=[[0]*5,[-1,0,0,0,0],[-1,-1,-1,0,0],[0,-1,0,-1,0]]
c=[[1,1,1,1,0],[1,1,1,0,0],[1,0,0,0,0],[0,1,0,1,0]]
cells=list(product(range(4),range(4),range(5)))
w=[a[i][j]+b[i][k]+c[j][k] for i,j,k in cells]
def col(t):
 i,j,k=t;v=[0]*56;v[4*i+j]=1;v[16+5*i+k]=1;v[36+5*j+k]=1;return v
def rank(rows):
 m=[[Q(x) for x in v] for v in rows];r=0
 for j in range(56):
  t=next((t for t in range(r,len(m)) if m[t][j]),None)
  if t is None:continue
  m[r],m[t]=m[t],m[r];s=m[r][j];m[r]=[x/s for x in m[r]]
  for t in range(r+1,len(m)):
   s=m[t][j]
   if s:m[t]=[x-s*y for x,y in zip(m[t],m[r])]
  r+=1
  if r==len(m):break
 return r
patterns=[[a[i][j]+b[i][k]+c[j][k]==0 for i,j in product(range(4),repeat=2)] for k in range(5)]
pairs={f'{k},{l}':next([i,j] for i,j in product(range(4),repeat=2) if patterns[k][4*i+j]!=patterns[l][4*i+j]) for k,l in combinations(range(5),2)}
result=dict(min=min(w),max=max(w),tight=w.count(0),rank_all=rank([col(t) for t in cells]),rank_tight=rank([col(t) for t,v in zip(cells,w) if v==0]),patterns=patterns,distinguishing_cells=pairs)
assert result['min']==0 and result['tight']==45 and result['rank_all']==44 and result['rank_tight']==43
# Negative controls for the arithmetic routine: zero rows and duplicated rows have expected rank.
assert rank([[0]*56])==0 and rank([col(cells[0])]*2)==1
(R/'outputs/exact.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
