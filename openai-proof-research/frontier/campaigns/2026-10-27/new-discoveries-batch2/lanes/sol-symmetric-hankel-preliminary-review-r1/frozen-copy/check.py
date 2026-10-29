import os,resource,signal,json
for key in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[key]='1'
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912))
resource.setrlimit(resource.RLIMIT_CPU,(20,20));signal.alarm(25)
import sympy as s
z,u=s.symbols('z u',real=True)
w=z**2*(u+z)/(1+u*z)
p=1+w+w**2/3-w**3/9
ps=s.series(p,z,0,5).removeO().expand()
a={1:s.Integer(1)}
for n in range(2,6):a[n]=s.expand(sum(ps.coeff(z,k)*a[n-k] for k in range(1,n) if (n-k)%2==1)/(n-(1 if n%2 else 0)))
H=2*a[2]*a[3]*a[4]-a[3]**3-a[4]**2+a[3]*a[5]-a[2]**2*a[5]
assert s.simplify(16*H+1+u**3/3-u**4)==0
A={n:s.factor(v.subs(u,s.Rational(1,4))) for n,v in a.items()}
h=H.subs(u,s.Rational(1,4));assert h==-s.Rational(769,12288)
assert -h-s.Rational(1,16)==s.Rational(1,12288)
# Independent literal 3x3 determinant.
assert s.det(s.Matrix([[1,A[2],A[3]],[A[2],A[3],A[4]],[A[3],A[4],A[5]]]))==h
# Verify f built by analytic primitives satisfies its ODE to finite order only.
pe=(ps+ps.subs(z,-z))/2
G=s.integrate((pe-1)/z,z);odd=s.series(z*s.exp(G),z,0,7).removeO()
fprime=s.series(ps*odd/z,z,0,5).removeO();f=s.integrate(fprime,z)
assert all(s.simplify(f.coeff(z,n)-a[n])==0 for n in range(1,6))
y=s.symbols('y',real=True)
R=6+12*z+6*z**2-4*z**3
assert s.expand(R.subs(z,-y)-6*(1-y)**2-4*y**3)==0
assert s.expand(R-6-12*z-2*z**2-4*z**2*(1-z))==0
# Mobius disk identity with z=x+iy.
x,y=s.symbols('x y',real=True);v=x+s.I*y
assert s.expand((1+u*v)*(1+u*s.conjugate(v))-(u+v)*(u+s.conjugate(v))-(1-u*u)*(1-x*x-y*y))==0
out={'status':'PASS','coefficients':{str(k):str(v) for k,v in A.items()},'H':str(h),'strict_gap':str(-h-s.Rational(1,16)),'general_16H':str(s.factor(16*H)),'checks':'symbolic recurrence, independent determinant, primitive coefficients, boundary positivity and Mobius identity; no finite enumeration','limits':{'AS':536870912,'CPU':20,'wall_alarm':25,'BLAS':1}}
print(json.dumps(out,indent=2))
