from pathlib import Path
from fractions import Fraction as F
from math import gcd,lcm
import json
L=Path(__file__).resolve().parent
families=[(3,0,3,1,6,-1),(6,1,6,2,9,3),(6,1,9,2,9,3),(6,1,6,3,6,5),(6,1,12,-4,12,0),(3,1,6,-1,6,0),(3,2,3,3,3,4),(12,2,12,4,18,3),(3,2,6,1,6,3),(6,3,6,5,12,4),(6,4,6,5,9,6),(12,4,18,3,18,5),(6,5,9,6,9,7),(6,5,12,4,12,6),(12,8,12,10,18,15),(12,8,18,13,18,15)]
def match(T):
 a,b,d=T;out=[]
 for i,(u,v,w,x,y,z) in enumerate(families,1):
  if (a-v)%u:continue
  k=(a-v)//u
  if k>=(2 if i==5 else 1) and (b,d)==(w*k+x,y*k+z):out.append([i,k])
 return out
def dpcheck(T,A):
 a=T[0];bound=max(A)+a+5;dp=[True]+[False]*bound
 for n in range(1,bound+1):dp[n]=any(n>=g and dp[n-g] for g in T)
 assert all(dp[n]==(n>=A[n%a]) for n in range(bound+1))
tested=[0,0]
for a in range(12,81):
 for t in range(1,a):
  if gcd(a,t)!=1:continue
  for typ,T in enumerate([(a,2*t,3*t),(a,a+t,3*t)]):
   if not a<T[1]<T[2]<2*a:continue
   A=[0]*a
   for j in range(a):
    A[j*t%a]=(a+1)*t if j==1 else j*t
    if typ:A[j*t%a]=min(((j+k*a)%3)*a+(j+k*a)*t for k in range(3))
   dpcheck(T,A);tested[typ]+=1
verts=[]
for v in json.loads((L/'arrangement-result.json').read_text())['surviving_vertices']:
 x,y=map(F,v['point']);a=lcm(x.denominator,y.denominator);T=(a,int(a*x),int(a*y));g=gcd(*T);T=tuple(z//g for z in T)
 if T[0]<12:continue
 # Independent direct DP up to a guaranteed conductor: a consecutive reachable block.
 a=T[0];dp=[True];run=0;n=0
 while run<a+5:
  n+=1;dp.append(any(n>=z and dp[n-z] for z in T));run=run+1 if dp[n] else 0
 seq=[j for j in range(1,len(dp)) if dp[j]]
 bad=next((seq[i:i+3] for i in range(0,len(seq)-2,3) if len({x%3 for x in seq[i:i+3]})<3),None)
 verts.append(dict(triple=T,bad=bad,families=match(T)))
(L/'apery-result.json').write_text(json.dumps(dict(DP_cases=tested,vertices=verts),indent=2)+'\n')
print('symbolic formulas DP',tested,'vertices',verts)
