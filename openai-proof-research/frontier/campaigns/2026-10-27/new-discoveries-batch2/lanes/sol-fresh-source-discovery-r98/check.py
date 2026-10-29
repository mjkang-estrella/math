from pathlib import Path
from math import comb
import json
P=Path(__file__).resolve().parent
N=81
rise=[[1]]
for a in range(N):
 v=rise[-1];w=[0]*(len(v)+1)
 for i,c in enumerate(v):w[i]+=a*c;w[i+1]+=c
 rise.append(w)
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
def add(a,b,w=1):return [x+w*y for x,y in zip(a,b)]
def defects(a):return [a[i]*a[i]-a[i-1]*a[i+1] for i in range(1,len(a)-1)]
first=None;count=0;source_cases=0;bad=[];fixed_real_gap=None
for n in range(3,N+1,2):
 r=(n-1)//2;B=[mul(rise[n-j],rise[j]) for j in range(r)]
 for j in range(r):
  for h in range(j+1,r):
   cross=[2*B[j][i]*B[h][i]-B[j][i-1]*B[h][i+1]-B[h][i-1]*B[j][i+1] for i in range(1,n)]
   count+=len(cross)
   if min(cross)<0 and first is None:
    i=next(i+1 for i,x in enumerate(cross) if x<0);first=dict(n=n,j=j,h=h,i=i,cross=str(cross[i-1]),a=list(map(str,B[j])),b=list(map(str,B[h])))
 for k in range(2*r-1):
  a=[0]*(n+1)
  for j in range(r):
   if j<=k<=2*r-2-j and (k-j)%2==0:a=add(a,B[j],comb(n,j))
  source_cases+=1
  if min(defects(a))<0:bad.append([n,k])
 a=[0]*(n+1)
 for j in range(r):a=add(a,B[j],(r-j)*comb(n,j))
 source_cases+=1
 if min(defects(a))<0:bad.append([n,'t1'])
out=dict(max_n=N,source_cases=source_cases,source_failures=bad,mixed_defects_checked=count,first_negative_mixed_defect=first,normalization='all source rows multiplied by n!; B_j=(m) rising (n-j) times (m) rising j')
(P/'check-results.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items() if k!='first_negative_mixed_defect'});print('first negative',None if first is None else {k:v for k,v in first.items() if k not in ['a','b']})
