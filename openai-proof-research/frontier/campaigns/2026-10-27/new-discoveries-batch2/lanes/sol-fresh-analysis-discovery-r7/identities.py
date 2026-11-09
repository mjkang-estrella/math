import os,resource
os.environ.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1')
resource.setrlimit(resource.RLIMIT_AS,(384*1024**2,384*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(60,60))
import sympy as s,json
from fractions import Fraction as Q
from pathlib import Path
x,j,e,b=s.symbols('x j e b',positive=True)
a=x/(j*j+e*x*(x-j))
assert s.cancel(s.diff(a,x)-(j*j-e*x*x)/(j*j+e*x*(x-j))**2)==0
f=1/(1-b*x+x*x)
assert s.cancel((f.subs(x,Q(1,2))-1)/2-(2*b-1)/(2*(5-2*b)))==0
assert s.cancel((f.subs(x,Q(1,2))-f.subs(x,1))/2-(3-2*b)/(2*(5-2*b)*(2-b)))==0
# Refute real-rooted numerator shortcut exactly: cubic discriminant <0.
num=72*b**3-378*b**2+655*b-370
disc=s.discriminant(num,b);assert disc<0
# Signed Stieltjes measure CDF changes sign already for n=2.
def cdf(n,r):return sum((Q(1,k) for k in range(1,n+1) if Q(k,n)>=r),Q(0))
cd=[str(cdf(2,r)-cdf(3,r)) for r in [Q(3,5),Q(7,10)]];assert cd==['-1/3','1/6']
# Check derived low-mesh bound against literal exact sums.
count=0
for n in range(1,31):
 eps=Q(1,4*(n+1)**2);bb=2-eps
 def vals(k):
  mid=sum((Q(k,1)/(k*k-bb*i*k+i*i) for i in range(1,k)),Q(0))
  return mid+Q(1,k),mid+1/(eps*k)
 L,R=vals(n);LL,RR=vals(n+1)
 bound=1/(eps*n*(n+1))-2-Q(2,n)
 assert R-RR>=bound>0 and LL>L
 count+=1
out={'derivative_identity':True,'first_difference_identities':True,'n2_numerator_discriminant':str(disc),'CDF_differences':cd,'exact_low_mesh_checks':count,'scope':'identities, route falsifiers, finite checks; not full theorem'}
Path(__file__).with_name('identity-checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
