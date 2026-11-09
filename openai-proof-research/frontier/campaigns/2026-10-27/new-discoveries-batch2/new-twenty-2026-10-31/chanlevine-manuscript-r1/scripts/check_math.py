from pathlib import Path
from itertools import product
from math import gcd,comb
import json
p=Path.cwd()
def divisors(n):return [d for d in range(1,n+1) if n%d==0]
def mu(n):
 v=1;d=2
 while d*d<=n:
  if n%d==0:
   n//=d;v=-v
   if n%d==0:return 0
   while n%d==0:n//=d
  d+=1
 return -v if n>1 else v
def ram(e,i):return sum(d*mu(e//d) for d in divisors(gcd(e,i)))
def mul(a,b,m):return [sum(a[j]*b[k-j] for j in range(max(0,k-len(b)+1),min(k+1,len(a)))) for k in range(m+1)]
def weight(n,m,e):
 r=n//e;q=0 if e%2 else 2*(-1)**(e//2);a=[0]*(m+1);a[0]=2
 b=a.copy()
 if e<=m:b[e]=q
 det=[0]*(m+1);det[0]=1
 if e<=m:det[e]=-2
 if 2*e<=m:det[2*e]=1
 for k in range(2,r+1):
  pb=mul(b,[2]+[0]*(e-1)+[q],m);da=mul(det,a,m);a,b=b,[x-y for x,y in zip(pb,da)]
 v=b if r else a
 return sum(v[m-e*j]*comb(r+j-1,j) for j in range(m//e+1))
def formula(n,m):
 vals=[sum(weight(n,m,e)*ram(e,i) for e in divisors(gcd(n,m))) for i in range(n)]
 assert all(v%n==0 for v in vals)
 return [v//n for v in vals]
def comps(m,n):
 if n==1:yield (m,);return
 for j in range(m+1):
  for c in comps(m-j,n-1):yield (j,)+c
def brute(n,m):
 ans=[0]*n
 for x in comps(m,n):
  for q in product([0,1],repeat=n): # 1 is right
   if any(q[k]==1 and q[(k+1)%n]==0 and x[k]+x[(k+1)%n]==0 for k in range(n)):continue
   ans[(sum(k*x[k] for k in range(n))+q.count(0))%n]+=1
 return ans
cases={}
for n in range(3,7):
 for m in range(1,5):
  a=brute(n,m);b=formula(n,m);assert a==b,(n,m,a,b);cases[f'{n},{m}']=a
expected={3:[26,24,24],4:[122,120,118,120],5:[642,640,640,640,640],6:[3630,3624,3624,3630,3624,3624],7:[21394,21392,21392,21392,21392,21392,21392],8:[130090,130080,130072,130080,130086,130080,130072,130080]}
for n,values in expected.items():assert formula(n,n)==values
for n in [3,4,5,6]:assert brute(n,n)==expected[n]
(p/'math-check.json').write_text(json.dumps({'all_passed':True,'independent_enumeration_cases':cases,'source_table_8_1':expected,'extra_brute_table_rows':[3,4,5,6],'diagnostic_only':True},indent=2)+'\n')
print('Exact enumeration/formula comparisons and all six Table 8.1 rows passed.')
