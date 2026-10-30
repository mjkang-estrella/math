import json,random,hashlib
from fractions import Fraction
from pathlib import Path
L=Path(__file__).resolve().parent
def comp(s):
 n=len(s);return tuple(sorted([0]+[n-x for x in s[1:]]))
def union(a,b):return tuple(sorted(a+b))
def test(s):
 n=len(s);t=comp(s);return [(k,s[-k]*t[-k]-n*(n-k)) for k in range(1,3*n//4+1)]
levels={1:{(0,)}};stats=[];fail=[];equal=0;comparisons=0
for n in range(2,13):
 ss=set()
 for a in range(1,n//2+1):
  for x in sorted(levels[a]):
   for y in sorted(levels[n-a]):
    z=union(x,y);ss.add(z);ss.add(comp(z))
 levels[n]=ss
 for s in sorted(ss):
  for k,d in test(s):
   comparisons+=1;equal+=d==0
   if d>0:fail.append(dict(n=n,k=k,spectrum=s,excess=d))
 stats.append([n,len(ss)])
r=random.Random(142);sample=[]
def tree(n):
 if n==1:return (0,)
 a=r.randrange(1,n);s=union(tree(a),tree(n-a));return comp(s) if r.randrange(2) else s
for i in range(5000):
 n=r.randrange(10,101);s=tree(n)
 for k,d in test(s):
  comparisons+=1
  if d>0:fail.append(dict(n=n,k=k,spectrum=s,excess=d))
 sample.append([n,hashlib.sha256(str(s).encode()).hexdigest()])
# Source Proposition19 negative controls are outside the asserted range.
controls=[]
for n in [12,13,20,21]:
 a=(n-1)//2;b=n-1-a
 # K1 join (Ka union Kb): complement formula applied to K1 union K_ab.
 cab=tuple(sorted([0,a+b]+[a]*(b-1)+[b]*(a-1)))
 s=comp(union((0,),cab));t=comp(s);k=(3*n)//4+1
 controls.append(dict(n=n,k=k,spectrum=s,excess=s[-k]*t[-k]-n*(n-k)))
 assert controls[-1]['excess']>0
# Scalar PSD/complement relaxation fails without graphicality.
relaxed=(0,0,1,4,4,5,6,6,9,9)
assert sum(relaxed)==44 and relaxed[-2]*comp(relaxed)[-2]==81>80
bc=[]
for s in [relaxed,comp(relaxed)]:
 m=Fraction(sum(s),2);bc.append(all(sum(s[-j:])<=m+Fraction(j*(j+1),2) for j in range(1,11)))
assert all(bc)
assert all(relaxed[-k]+comp(relaxed)[-k]>=10-k for k in range(1,10))
out=dict(exhaustive_cograph_distinct_spectra=stats,exhaustive_orders='1..12, spectra only; many nonisomorphic cographs share spectra',sampled_cographs=5000,sampled_orders='10..100 with repetitions, fixed seed142',sample_sha256=hashlib.sha256(json.dumps(sample).encode()).hexdigest(),integer_product_comparisons=comparisons,equality_occurrences_exhaustive=equal,violations=fail,source_negative_controls=controls,relaxed_spectrum=relaxed,relaxed_product=81,relaxed_bound=80,limits='Cographs only. No arbitrary-graph coverage; no universal proof. No numerical eigenvalues.')
out['relaxation_satisfies_all_Brouwer_prefix_bounds_both_sides']=bc
out['relaxation_satisfies_all_sum_Nordhaus_Gaddum_bounds']=True
def graph(n):
 if n==1:return [[0]],(0,)
 a=r.randrange(1,n);A,x=graph(a);B,y=graph(n-a);join=r.randrange(2)
 C=[[0]*n for _ in range(n)]
 for i in range(a):
  for j in range(a):C[i][j]=A[i][j]
 for i in range(n-a):
  for j in range(n-a):C[a+i][a+j]=B[i][j]
 if join:
  for i in range(a):
   for j in range(a,n):C[i][j]=C[j][i]=1
 s=union(x,y)
 if join:s=tuple(sorted([0,n]+[v+n-a for v in x[1:]]+[v+a for v in y[1:]]))
 return C,s
def det(A):
 A=[row[:] for row in A];d=1;sign=1;n=len(A)
 for k in range(n-1):
  if A[k][k]==0:
   j=next((j for j in range(k+1,n) if A[j][k]),None)
   if j is None:return 0
   A[k],A[j]=A[j],A[k];sign=-sign
  p=A[k][k]
  for i in range(k+1,n):
   for j in range(k+1,n):
    v=A[i][j]*p-A[i][k]*A[k][j];assert v%d==0;A[i][j]=v//d
  for i in range(k+1,n):A[i][k]=0
  d=p
 return sign*A[-1][-1]
matrix_checks=0
for rep in range(40):
 n=1+rep%10;A,s=graph(n);D=[sum(row) for row in A]
 for t in range(n+1):
  M=[[((t-D[i]) if i==j else A[i][j]) for j in range(n)] for i in range(n)]
  prod=1
  for v in s:prod*=t-v
  assert det(M)==prod;matrix_checks+=1
out['independent_characteristic_polynomial_checks']=dict(graphs=40,orders='1..10 repeated four times',integer_determinant_evaluations=matrix_checks,method='n+1 distinct integer points verify equality of monic degree-n characteristic polynomials; fraction-free determinant on directly constructed adjacency Laplacians')
(L/'check-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
