from pathlib import Path
from math import comb
import json
D=Path(__file__).resolve().parents[1]
b=[sum(2*comb(n+1,k-1)*comb(n+1,k)*comb(n+1,k+1) for k in range(1,n+1))//(n*(n+1)**2) for n in range(1,61)]
def det(a):
 n=len(a);a=[r[:] for r in a];old=1;sign=1
 for k in range(n-1):
  if not a[k][k]:
   j=next((j for j in range(k+1,n) if a[j][k]),None)
   if j is None:return 0
   a[k],a[j]=a[j],a[k];sign=-sign
  pivot=a[k][k]
  for i in range(k+1,n):
   for j in range(k+1,n):
    z=a[i][j]*pivot-a[i][k]*a[k][j];assert z%old==0;a[i][j]=z//old
  for i in range(k+1,n):a[i][k]=0
  old=pivot
 return sign*a[-1][-1]
rows=[]
for shift in [0,1]:
 for n in range(1,21):
  d=det([[b[i+j+shift] for j in range(n)] for i in range(n)]);rows.append({'shift':shift,'size':n,'determinant':str(d)})
(D/'outputs/baxter-hankel.json').write_text(json.dumps(rows,indent=2)+'\n');print('negative Hankel determinants',[(r['shift'],r['size']) for r in rows if int(r['determinant'])<0],flush=True)
a=b[:];rows=[]
for r in range(1,19):
 a=[a[i]*a[i+2]-a[i+1]**2 for i in range(len(a)-2)];row={'r':r,'n_range':[1,len(a)],'negative_indices':[i+1 for i,x in enumerate(a) if x<0],'largest_integer_bits':max(x.bit_length() for x in a)};rows.append(row);print(row,flush=True);(D/'outputs/baxter-higher.json').write_text(json.dumps(rows,indent=2)+'\n')
