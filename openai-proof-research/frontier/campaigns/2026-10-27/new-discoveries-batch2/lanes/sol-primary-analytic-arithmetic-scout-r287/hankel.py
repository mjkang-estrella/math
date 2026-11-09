from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json,time
L=Path(__file__).resolve().parent;start=time.monotonic();N=65
def enc(q):return {'numerator_hex':hex(q.numerator),'denominator_hex':hex(q.denominator)}
# Congruence scaling by i! keeps intermediate entries smaller. Exact rational LDL.
A=[[F(factorial(i+j),factorial(i)*factorial(j)*((i+j)**2+i+j+1)) for j in range(N)] for i in range(N)]
D=[];LL=[[F(i==j) for j in range(N)] for i in range(N)];rows=[]
for j in range(N):
 d=A[j][j]-sum(LL[j][k]**2*D[k] for k in range(j));D.append(d);rows.append(dict(index=j,sign=(d>0)-(d<0),numerator_bits=d.numerator.bit_length(),denominator_bits=d.denominator.bit_length()))
 print(j,rows[-1]['sign'],flush=True)
 if d<=0:
  if d<0:
   # Solve L^t v=e_j, so v^t A v=d.
   v=[F(0)]*(j+1);v[j]=F(1)
   for i in range(j-1,-1,-1):v[i]=-sum(LL[k][i]*v[k] for k in range(i+1,j+1))
   r=[v[i]/factorial(i) for i in range(j+1)];c=[F(0)]*(2*j+1)
   for i,a in enumerate(r):
    for k,b in enumerate(r):c[i+k]+=a*b
   eps=-d/2;c[0]+=eps
   p=[z*F(factorial(k),k*k+k+1) for k,z in enumerate(c)]
   assert sum(p)==d/2<0 and p[-1]>0
   (L/'moment-witness.json').write_text(json.dumps(dict(index=j,r=list(map(enc,r)),negative_form=enc(d),epsilon=enc(eps),input=list(map(enc,p)),output=list(map(enc,c)),input_at_one=enc(sum(p))),indent=2))
  break
 for i in range(j+1,N):LL[i][j]=(A[i][j]-sum(LL[i][k]*LL[j][k]*D[k] for k in range(j)))/d
 if time.monotonic()-start>180:break
(L/'hankel-checks.json').write_text(json.dumps(dict(cap=N,rows=rows,elapsed=time.monotonic()-start,arithmetic='Fraction exact LDL with factorial congruence scaling'),indent=2))
