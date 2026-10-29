exec(open(__file__.replace('route.py','check.py')).read().split('first=None')[0])
import sympy as sp
x=sp.Symbol('m');out={};first=None
for n in range(3,N+1,2):
 r=(n-1)//2;a=mul(rise[n],rise[0]);b=mul(rise[n-r+1],rise[r-1])
 for i in range(1,n):
  da=a[i]**2-a[i-1]*a[i+1]; db=b[i]**2-b[i-1]*b[i+1]; c=2*a[i]*b[i]-a[i-1]*b[i+1]-b[i-1]*a[i+1]
  if c<0 and c*c>4*da*db:
   from fractions import Fraction
   w=Fraction(-c,2*db);d=Fraction(da)+w*c+w*w*db
   first=dict(n=n,j=0,h=r-1,index=i,weight=str(w),defect=str(d),a=list(map(str,a)),b=list(map(str,b)))
   break
 if first:break
out['arbitrary_positive_mixture_counterexample']=first
# Stronger real-rootedness shortcut, on actual prescribed source rows.
rootfail=None
for n in range(3,26,2):
 r=(n-1)//2
 for k in range(r):
  a=[0]*(n+1)
  for j in range(k+1):
   if (k-j)%2==0:a=add(a,mul(rise[n-j],rise[j]),comb(n,j))
  f=sp.Poly.from_list(list(reversed(a)),x); nr=f.count_roots(-sp.oo,sp.oo)
  # count_roots counts distinct; use squarefree decomposition for multiplicities
  real=sum(m*g.count_roots(-sp.oo,sp.oo) for g,m in f.sqf_list()[1])
  if real<f.degree():rootfail=dict(n=n,k=k,degree=f.degree(),real_roots_multiplicity=int(real),coefficients=list(map(str,a)));break
 if rootfail:break
out['source_row_real_rootedness_failure']=rootfail
# Verify bivariate generating function by direct rising factorial coefficients at m=1,2,3.
identities=0
for n in range(3,22,2):
 r=(n-1)//2
 for m in range(1,4):
  for k in range(2*r-1):
   v=sum(comb(m+n-j-1,n-j)*comb(m+j-1,j) for j in range(r) if j<=k<=2*r-2-j and (k-j)%2==0)
   kk=min(k,2*r-2-k)
   rhs=sum(comb(m+n-j-1,n-j)*comb(m+j-1,j) for j in range(kk+1) if (kk-j)%2==0)
   assert v==rhs;identities+=1
out['symmetry_prefix_identity_checks']=identities
(P/'route-results.json').write_text(json.dumps(out,indent=2));print({k:({a:b for a,b in v.items() if a not in ['a','b','coefficients']} if isinstance(v,dict) else v) for k,v in out.items()})
