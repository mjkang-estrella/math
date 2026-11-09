import pathlib,json
from fractions import Fraction as F
P=pathlib.Path(__file__).resolve().parent
mul={(0,j):{j:1} for j in range(4)};mul.update({(j,0):{j:1} for j in range(4)});mul.update({(1,2):{3:-2},(2,1):{3:1}})
def rank(n):
 a=[[F(0) for _ in range(4*n)] for _ in range(4*(n+1))]
 for i in range(n+1):
  for col in range(4*n):
   j,b=divmod(col,4)
   terms=[]
   if j==i:terms +=[(1,b,1),(b,1,(-1)**n*2**i)]
   if j==i-1:terms +=[(2,b,2**(n-i)),(b,2,(-1)**n)]
   for u,v,c in terms:
    for k,x in mul.get((u,v),{}).items():a[4*i+k][col]+=c*x
 r=0
 for c in range(4*n):
  piv=next((k for k in range(r,len(a)) if a[k][c]),None)
  if piv is None:continue
  a[r],a[piv]=a[piv],a[r];z=a[r][c];a[r]=[v/z for v in a[r]]
  for k in range(r+1,len(a)):
   z=a[k][c]
   if z:a[k]=[v-z*w for v,w in zip(a[k],a[r])]
  r+=1
 return r
r={0:0,**{n:rank(n) for n in range(1,10)}};dims={n:4*(n+1)-r[n]-r[n+1] for n in range(9)}
assert list(dims.values())==[2,2,1,0,0,0,0,0,0]
(P/'bounded-checks.json').write_text(json.dumps(dict(executed=True,field='Q',q=2,differential_ranks=r,HH_dimensions=dims,scope='Finite replay n=0..8 of the published resolution differential; not all-degree proof or resolution exactness validation; prior exclusion only.',brownian_22=str(F((7+7-2)**2-4,48))),indent=2)+'\n')
print(dims)
