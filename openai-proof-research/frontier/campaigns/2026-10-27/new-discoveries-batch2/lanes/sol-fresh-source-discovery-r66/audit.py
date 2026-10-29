from functools import lru_cache
from itertools import product,permutations
from fractions import Fraction as F
from math import comb
import json,pathlib,sys
L=pathlib.Path(__file__).resolve().parent
exact='--exact' in sys.argv
params=[(F(1,3),F(2,3)),(F(2,3),F(1,3)),(F(1,2),F(1,2))] if exact else [(q,t) for q in [.01,.1,.5,.9,.99] for t in [.01,.1,.5,.9,.99]]
def parts(d,n,m=None):
 if not n:
  if d==0:yield ()
  return
 for a in range(min(d,m if m is not None else d),-1,-1):
  for b in parts(d-a,n-1,a):yield (a,)+b
records=[];fails=[];count=0; eigen=0; row=0; shifted=0; coeff_fail=[]
for q,t in params:
 one=F(1) if exact else 1.
 @lru_cache(None)
 def b(l,i,j):
  arm=l[i]-j;leg=sum(x>=j for x in l[i+1:])
  return (1-q**arm*t**(leg+1))/(1-q**(arm+1)*t**leg)
 @lru_cache(None)
 def psi(l,m):
  mp=m+(0,); rows=[i for i in range(len(l)) if l[i]>mp[i]]
  cols={j for i in rows for j in range(mp[i]+1,l[i]+1)}
  v=one
  for i in rows:
   for j in range(1,mp[i]+1):
    if j not in cols:v*=b(m,i,j)/b(l,i,j)
  return v
 @lru_cache(None)
 def poly(l,n):
  if n==0:return {():one} if not sum(l) else {}
  ans={}
  # interlacing mu, n-1 parts
  if l[-1]!=0 and len(l)>n:return ans
  lp=l+(0,)
  for m in product(*(range(lp[i+1],lp[i]+1) for i in range(n-1))):
   if n==1 and any(l[1:]):continue
   w=psi(l,m);k=sum(l)-sum(m)
   for e,c in poly(m,n-1).items():ans[e+(k,)]=ans.get(e+(k,),0)+c*w
  return ans
 maxn=4 if exact else 5
 maxd=6 if exact else 10
 for n in range(2,maxn+1):
  for d in range(1,maxd+1):
   for l in parts(d,n):
    if l[0]==l[-1]:continue
    p=poly(l,n)
    # independent symmetry check on full coefficient body
    for e,c in p.items():
     ee=e[1:]+e[:1]
     assert abs(float(c-p.get(ee,0)))<1e-7*max(1,abs(float(c))), (q,t,l,e,c,p.get(ee,0))
    if exact:
     from math import prod
     def ev(z):return sum(c*prod(v**k for v,k in zip(z,e)) for e,c in p.items())
     z=[F(j+1) for j in range(n)]
     Dz=F(0)
     for j in range(n):
      zz=z[:];zz[j]*=q
      Dz+=prod((t*z[j]-z[k])/(z[j]-z[k]) for k in range(n) if k!=j)*ev(zz)
     assert Dz==sum(q**l[j]*t**(n-j-1) for j in range(n))*ev(z)
     eigen+=1
    C=[]
    for i in range(n+1):
     a=[one*0 for _ in range(d+1)]
     for e,c in p.items():a[sum(e[:i])]+=c*t**sum(j*v for j,v in enumerate(e))
     C.append(a)
    if exact:
     def mul(a,b):
      c=[F(0)]*(len(a)+len(b)-1)
      for k,u in enumerate(a):
       for j,v in enumerate(b):c[k+j]+=u*v
      return c
     def add(a,b):return [(a[k] if k<len(a) else 0)+(b[k] if k<len(b) else 0) for k in range(max(len(a),len(b)))]
     def der(a):return [k*a[k] for k in range(1,len(a))]
     for i in range(1,n):
      aa,bb,cc=C[i-1:i+2]
      left=mul(mul(der(bb),aa),cc);right=mul(bb,add(mul(der(aa),cc),mul(aa,der(cc))))
      N=add([2*u for u in left],[-u for u in right]);W=[sum(N[k]*comb(k,j) for k in range(j,len(N))) for j in range(len(N))]
      shifted+=1
      if any(w<0 for w in W):coeff_fail.append({'q':str(q),'t':str(t),'lambda':l,'n':n,'i':i})
     if l[1:]==(0,)*(n-1):
      def poch(a,m):return prod(1-a*q**r for r in range(m))
      # P=Q/b_lambda, b_lambda=(t;q)_d/(q;q)_d
      norm=poch(t,d)/poch(q,d)
      for i in range(n+1):
       expected=[poch(t**i,k)*poch(t**(n-i),d-k)*t**(i*(d-k))/(poch(q,k)*poch(q,d-k))/norm for k in range(d+1)]
       assert C[i]==expected
       row+=1
    def val(a,x):return sum(c*x**k for k,c in enumerate(a))
    def slope(a,x):return sum(k*c*x**k for k,c in enumerate(a))
    xs=[F(11,10),F(2),F(10)] if exact else [1.001,1.1,2.,10.,100.]
    for i in range(1,n):
     for x in xs:
      vs=[val(C[j],x) for j in [i-1,i,i+1]];ds=[slope(C[j],x) for j in [i-1,i,i+1]]
      D=2*ds[1]/vs[1]-ds[0]/vs[0]-ds[2]/vs[2];count+=1
      if exact: assert D>0
      if D<(-1e-9 if not exact else 0):fails.append({'q':str(q),'t':str(t),'n':n,'lambda':l,'i':i,'x':str(x),'D':str(D)})
    # preserve a full exact representative coefficient array
    if exact and l==(2,1,0) and q!=t:records.append({'q':str(q),'t':str(t),'lambda':l,'C':[[str(c) for c in a] for a in C]})
 print(json.dumps({'q':str(q),'t':str(t),'checks':count,'failures':len(fails)}),flush=True)
 if fails:break
(L/('audit.json' if exact else 'audit-float.json')).write_text(json.dumps({'checks':count,'failures':fails,'representatives':records,'finite_only':True,'eigen_checks':eigen,'one_row_arrays':row,'shifted_N_checks':shifted,'shifted_N_failures':coeff_fail},indent=2))
