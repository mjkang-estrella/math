from pathlib import Path
from math import comb
import json
L=Path(__file__).resolve().parent
out=[]
for a,b in [(3,9),(3,21),(3,51),(5,21),(7,51)]:
 n=a+b;states=[(i,j) for i in range(a+1) for j in range(b+1)];moves=[]
 for s,(i,j) in enumerate(states):
  row=[]
  if 2*j>b and i<a:row.append(((i+1)*(b+1)+j,a-i))
  if 2*j<b and i>0:row.append(((i-1)*(b+1)+j,i))
  if 2*i>a and j<b:row.append((s+1,b-j))
  if 2*i<a and j>0:row.append((s-1,j))
  row.append((s,n-sum(r for z,r in row)));moves.append(row)
 w=[comb(a,i)*comb(b,j)*3**(n-i-j) for i,j in states]
 w2=[x*((16*(i+j)-4*n)**2-128*(i+j)-16*n) for x,(i,j) in zip(w,states)]
 for side in [0,1]:
  f=[s[side] for s in states];h=sum(x*y for x,y in zip(w,f));badtime=[];badcurve=[]
  for k in range(201):
   c=sum(x*y for x,y in zip(w2,f))
   if c<0:badcurve.append(k)
   nf=[sum(r*f[z] for z,r in row) for row in moves];nh=sum(x*y for x,y in zip(w,nf))
   if nh-n*h>0:badtime.append(k)
   f=nf;h=nh
  out.append(dict(a=a,b=b,p='1/4',side=side,steps=201,positive_time_coefficients=badtime,negative_curvature_coefficients=badcurve))
(L/'exact-results.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
