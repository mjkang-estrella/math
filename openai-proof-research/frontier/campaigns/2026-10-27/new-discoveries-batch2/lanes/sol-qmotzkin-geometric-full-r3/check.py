#!/usr/bin/env python3
"""Exact identities and counterexamples to proposed proof mechanisms; no grid."""
import os,resource,json,itertools
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(60,60))
for v in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):os.environ[v]='1'
from sympy import ZZ
from sympy.polys.rings import ring
from pathlib import Path
R,t=ring('t',ZZ)
N=12
# f_n(x)=q^(-n(n-1)/2) p_n(x), with t=1/q.
f=[[R.one],[ -R.one,R.one]]
for n in range(1,N):
 a=[R.zero]*(n+2)
 for j,c in enumerate(f[n]):a[j]-=c;a[j+1]+=t**n*c
 for j,c in enumerate(f[n-1]):a[j]-=c
 f.append(a)
# Independent product coefficient construction, no orthogonal recurrence.
def productcoeff(j,d):
 a=[R.one]+[R.zero]*d
 for ell in range(j+1):
  # 1/(1+t^ell z+t^(2ell) z^2)=(1-t^ell z)/(1-t^(3ell) z^3)
  h=[R.zero]*(d+1)
  for m in range(d//3+1):
   h[3*m]=t**(3*ell*m)
   if 3*m+1<=d:h[3*m+1]=-t**(ell*(3*m+1))
  a=[sum((a[v]*h[u-v] for v in range(u+1)),R.zero) for u in range(d+1)]
 return t**(j*(j-1)//2)*a[d]
for n in range(N+1):
 for j in range(n+1):assert f[n][j]==productcoeff(j,n-j)
out={'limits':{'AS_MiB':512,'CPU_seconds':60,'BLAS_threads':1},'product_formula_coefficient_checks':sum(n+1 for n in range(N+1)),'status':'PASS','f_first':[ [str(c) for c in row] for row in f[:8]]}
# Locate a mixed coefficient to falsify any row/column scalar sign repair.
mixed=[{'n':n,'j':j,'polynomial':str(c)} for n,row in enumerate(f) for j,c in enumerate(row) if any(v<0 for v in c.values()) and any(v>0 for v in c.values())]
assert f[6][3]==t**12-t**8-t**7+t**3
assert f[6][3]==t**3*(1-t**4)*(1-t**5)
out['mixed_entries']=mixed[:3]
# Exact complementary-minor Christoffel bridge, selected nonsymmetric shapes.
def det(a):
 n=len(a)
 if n==0:return R.one
 a=[row[:] for row in a];prev=R.one;sgn=1
 for k in range(n-1):
  if not a[k][k]:
   h=next((i for i in range(k+1,n) if a[i][k]),None)
   if h is None:return R.zero
   a[k],a[h]=a[h],a[k];sgn=-sgn
  pivot=a[k][k]
  for i in range(k+1,n):
   for j in range(k+1,n):a[i][j]=(a[i][j]*pivot-a[i][k]*a[k][j]).exquo(prev)
   a[i][k]=R.zero
  prev=pivot
 return sgn*a[-1][-1]
# work in t directly for original monic recurrence with q=t
p=[[R.one],[-R.one,R.one]]
for n in range(1,10):
 a=[R.zero]*(n+2)
 for j,c in enumerate(p[n]):a[j]-=t**n*c;a[j+1]+=c
 for j,c in enumerate(p[n-1]):a[j]-=t**(2*n-1)*c
 p.append(a)
M=[R.one]
for m in range(15):M.append(M[m]+sum((t**(r+1)*M[r]*M[m-1-r] for r in range(m)),R.zero))
out['Christoffel_checks']=[]
for n,r in [(1,6),(3,4),(4,3),(2,5)]:
 a=[[p[n+j][i] if i<len(p[n+j]) else R.zero for j in range(r)] for i in range(r)]
 d=det([[M[r+i+j] for j in range(n)] for i in range(n)])
 e=(-1)**(n*r)*t**sum(i*i for i in range(n))*det(a)
 assert d==e
 out['Christoffel_checks'].append({'n':n,'r':r,'PASS':True})
# Geometric coefficient-array 2x2 minors, as an obstruction, not target values.
minors=[]
for rows in itertools.combinations(range(4),2):
 for cols in itertools.combinations(range(1,8),2):
  def at(i,j):return f[j][i] if i<len(f[j]) else R.zero
  d=at(rows[0],cols[0])*at(rows[1],cols[1])-at(rows[0],cols[1])*at(rows[1],cols[0])
  if any(c<0 for c in d.values()) and any(c>0 for c in d.values()):
   minors.append({'rows':rows,'columns':cols,'polynomial':str(d)})
assert f[3][0]*f[4][2]-f[4][0]*f[3][2]==t**4-t
assert p[6][3]==t**3-t**7-t**8+t**12
assert p[3][0]*p[4][2]-p[4][0]*p[3][2]==t**5-t**8
# a^2+a+1=0 makes (1+a)^2=a, exactly the q-Lommel scaling condition.
A,a=ring('a',ZZ);assert ((1+a)**2-a).rem(a*a+a+1)==0
out['cube_root_scaling_identity']='PASS exact remainder zero'
out['mixed_coefficient_minors']=minors[:3]
Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
