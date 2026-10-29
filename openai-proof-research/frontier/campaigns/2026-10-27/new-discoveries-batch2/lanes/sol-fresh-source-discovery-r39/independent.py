import os,signal,resource,pathlib,json
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(30,30));signal.alarm(40)
import sympy as s
x,t=s.symbols('x t');n=s.symbols('n',integer=True,positive=True);c=(n+2)*(n+3)/2
q=(x*x+x/s.Integer(100)+1)**2
T=lambda q,n:s.expand(2*x**3*s.diff(q,x,2)+((2*n+7)*x*x+x)*s.diff(q,x)+((n+2)*(n+3)*x/2+1)*q)
p=T(q,6); coeff=s.Poly(p,x).all_coeffs()
H=s.Matrix(5,5,lambda i,j:coeff[2*j-i+1] if 0<=2*j-i+1<=5 else 0)
dets=[s.factor(H[:k,:k].det(method='bareiss')) for k in range(1,6)]
assert dets[3]<0
# Independent algebra check of coupled even/odd recurrence on a generic degree-8 polynomial.
e=s.symbols('e:5');o=s.symbols('o:4');E=sum(e[i]*t**i for i in range(5));O=sum(o[i]*t**i for i in range(4));generic=E.subs(t,x*x)+x*O.subs(t,x*x)
En=E+2*t*s.diff(E,t)+(c+2*n+7)*t*O+(4*n+26)*t*t*s.diff(O,t)+8*t**3*s.diff(O,t,2)
On=2*O+2*t*s.diff(O,t)+c*E+(4*n+18)*t*s.diff(E,t)+8*t*t*s.diff(E,t,2)
assert s.expand(T(generic,n)-En.subs(t,x*x)-x*On.subs(t,x*x))==0
out={'input_factor':'(x^2+x/100+1)^2; all roots real part -1/200','image':str(p),'hurwitz_determinants':[str(v) for v in dets],'negative_Delta4':True,'coupled_even_odd_identity':True,'scope':'route obstruction only'}
b=pathlib.Path(__file__).parent;(b/'independent.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
