"""Exact Gaussian integer cumulants for Area's formal Definition 2.1.
No discovery or all-order theorem is claimed by this finite experiment.
"""
from math import comb, factorial
from pathlib import Path
import json

def add(p,q,c=1):
 r=p.copy()
 for a,(x,y) in q.items():
  u,v=r.get(a,(0,0));r[a]=(u+c*x,v+c*y)
 return {a:z for a,z in r.items() if z!=(0,0)}
def scale(p,z):
 a,b=z;return {k:(a*x-b*y,a*y+b*x) for k,(x,y) in p.items() if (x,y)!=(0,0)}
def mul(p,q):
 r={}
 for (a,b),(x,y) in p.items():
  for (c,d),(u,v) in q.items():
   k=(a+c,b+d);s,t=r.get(k,(0,0));r[k]=(s+x*u-y*v,t+x*v+y*u)
 return {a:z for a,z in r.items() if z!=(0,0)}
def vp(n):
 n=abs(n);return (n&-n).bit_length()-1 if n else 10**9

def compute(N, return_cumulants=False):
 P=[{(0,0):(1,0)}];Q=[P[0]]
 for j in range(N):
  P.append(mul(P[-1],{(1,0):(1,0),(0,0):(-j*(j+1),0)}))
  Q.append(mul(Q[-1],{(0,1):(1,0),(0,0):(-j*(j+1),0)}))
 plus=[(1,0)];minus=[(1,0)]
 for j in range(N):
  a,b=plus[-1];plus.append((a-b,a+b));a,b=minus[-1];minus.append((a+b,b-a))
 S=[[0]*(N+1) for _ in range(N+1)];S[0][0]=1
 for n in range(1,N+1):
  for m in range(1,n+1):S[n][m]=S[n-1][m-1]+m*S[n-1][m]
 C=[]
 for m in range(N+1):
  c={}
  for l in range(m+1):
   a,b=plus[l];x,y=minus[m-l];z=(a*x-b*y,a*y+b*x)
   c=add(c,scale(mul(P[l],Q[m-l]),z),comb(m,l))
  C.append(c)
 A=[];B=[{}];rows=[]
 for n in range(N+1):
  p={}
  for m in range(n+1):p=add(p,C[m],S[n][m]*2**(n-m)*(factorial(n)//factorial(m)))
  A.append(p)
  if n==0:continue
  b=p
  for k in range(1,n):b=add(b,mul(B[k],A[n-k]),-comb(n-1,k-1))
  B.append(b)
  if n%2:
   v=min(vp(z[1]) for z in b.values());r=(n+1)//2
   row={'r':r,'n':n,'min_v2_imag_cumulant':v,'proposed':3*(r-1),'delta':2*n+vp(factorial(n))-v,'predicted_delta':2*r+vp(factorial(r-1)),'nonzero_imag_coefficients':sum(z[1]!=0 for z in b.values())}
   rows.append(row);print(json.dumps(row),flush=True)
 return (rows, B) if return_cumulants else rows
if __name__=='__main__':
 rows=compute(23)
 Path('shifted-content-check.json').write_text(json.dumps({'scope':'Finite exact experiment only, NOT a theorem; formal kappa Definition2.1, not unproved all-order actual phase identification','rows':rows},indent=2)+'\n')
