from itertools import product
from pathlib import Path
import json
D=Path(__file__).resolve().parents[1];out=[]
for k in range(1,11):
 count=0;bad=0;zeros=[0]*(3*k)
 for choices in product(range(3),repeat=k):
  z=[0]*k;i=0
  while i<k:
   if choices[i]!=2:i+=1;continue
   j=i
   while j<k and choices[j]==2:j+=1
   for h in range(i,j):z[h]=(h-i+1)*(j-h)
   i=j
  x=[0]*k;y=[0]*k
  for i,c in enumerate(choices):
   t=2+(z[i-1]if i else 0)+(z[i+1]if i+1<k else 0)-2*z[i]
   if c==0:x[i]=t
   if c==1:y[i]=t
  for i in range(k):
   if x[i]+y[i]+2*z[i]-(z[i-1]if i else 0)-(z[i+1]if i+1<k else 0)!=2:bad+=1
   if sum(v>0 for v in [x[i],y[i],z[i]])!=1:bad+=1
  count+=1
 r=dict(d=k+2,k=k,vertices=count,violations=bad,facets=3*k,face_vector=[sum(1 for _ in [])]);r['face_vector']=[1]
 # coefficients (3+3t+t^2)^k, source convention nonempty faces
 poly=[1]
 for _ in range(k):
  q=[0]*(len(poly)+2)
  for i,a in enumerate(poly):
   for j,b in enumerate([3,3,1]):q[i+j]+=a*b
  poly=q
 r['face_vector']=poly;out.append(r);print(r,flush=True)
(D/'outputs/ferrers.json').write_text(json.dumps(out,indent=2)+'\n')
