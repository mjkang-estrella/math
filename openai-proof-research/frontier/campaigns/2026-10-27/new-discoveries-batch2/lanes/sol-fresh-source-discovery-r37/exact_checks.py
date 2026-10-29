import os,resource,signal,json,pathlib
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']: os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(40,40));signal.alarm(55)
import sympy as s
x,y=s.symbols('x y')
def R(n,a,b):
 return s.Poly(s.expand(sum(s.rf(-n,k)*s.rf(n-a-b-1,k)*s.rf(-x,k)*s.rf(-y+k,n-k)/(s.rf(-a,k)*s.factorial(k)) for k in range(n+1))),x,y)
def H(p):
 n=p.total_degree();return s.Poly(sum(c*x**i*y**j for (i,j),c in p.terms() if i+j==n),x,y)
count=0;grid=0
for n in range(2,8):
 for a in range(n,n+4):
  for b in range(a,n+4):
   p=R(n,a,b);fac=s.factor_list(p.as_expr())[1]
   degs=sorted([s.Poly(q,x,y).total_degree() for q,e in fac for _ in range(e)])
   assert degs==sorted([1,n-1] if a==b and n%2 else [n]);count+=1
   assert s.expand(p.as_expr().subs(x,0)-s.rf(-y,n))==0
   C=(-1)**n*s.rf(-b,n)/s.rf(-a,n)
   assert s.expand(p.as_expr().subs(x,y)-C*s.rf(-y,n))==0
   for j in range(n):
    for i in range(j+1):assert p.eval({x:i,y:j})==0;grid+=1
for n in range(2,16):
 p=H(R(n,n,n)).as_expr()
 assert s.expand(y*p-x**(n+1)+(x-y)**(n+1))==0
# Nonexceptional leading-form obstruction, n=8.
p=R(8,8,8); assert len(s.factor_list(H(p).as_expr())[1])==2
assert len(s.factor_list(p.as_expr())[1])==1
# A specialization cannot prove this irreducible bivariate example.
p=R(2,2,8).as_expr();assert s.expand(p.subs(y,-1)-2*(3*x-1)*(6*x-1))==0
assert len(s.factor_list(p)[1])==1
# Exact smoothness diagnostics, not a uniform claim.
smooth=[]
for n,a,b in [(3,3,4),(4,4,4),(4,4,5),(5,5,6),(6,6,6)]:
 p=R(n,a,b);expr=p.as_expr()
 assert list(s.groebner([expr,s.diff(expr,x),s.diff(expr,y)],x,y))==[1]
 h=H(p).as_expr().subs(y,1)
 assert s.gcd(h,s.diff(h,x))==1
 assert H(p).coeff_monomial(x**n)!=0
 smooth.append([n,a,b])
# Lattice and two boundary restrictions alone allow reducibility.
n,a,b=4,4,5;C=(-1)**n*s.rf(-b,n)/s.rf(-a,n)
F=(y-(1-C)*x)*s.prod(y-j for j in range(1,n))
assert s.expand(F.subs(x,0)-s.rf(-y,n))==0
assert s.expand(F.subs(x,y)-C*s.rf(-y,n))==0
for j in range(n):
 for i in range(j+1):assert F.subs({x:i,y:j})==0
out={'status':'PASS','diagnostic_only':True,'bivariate_factor_cases':count,'triangular_grid_zeros':grid,'diagonal_leading_form_identities':14,'nonexceptional_n8_leading_form_factors':str(s.factor(H(R(8,8,8)).as_expr())),'specialization_obstruction':str(s.factor(R(2,2,8).as_expr())),'smooth_projective_examples':smooth,'scope':'No universal Hahn proof or source counterexample'}
pathlib.Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
