import os
os.environ.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1')
import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(60,60))
import sympy as s,json
from fractions import Fraction as F
from pathlib import Path
x,e,a=s.symbols('x e a',real=True);z=e/2+s.I*a
assert s.expand(z*s.conjugate(z)).subs(a*a,e-e*e/4).simplify()==e
j,n=s.symbols('j n',real=True)
partial=(1/(j-n*z)-1/(j-n*s.conjugate(z)))/(2*s.I*a)
assert s.factor(partial-n/(j*j-e*n*j+e*n*n)).subs(a*a,e-e*e/4).simplify()==0
q=1-s.Rational(3,2)*x+x*x
h=x/q**2;H=(h+h.subs(x,1-x))/2
curv=[s.diff(H,x,2).subs(x,v) for v in [0,s.Rational(1,2),1]]
assert curv==[-9,12,-9]
def phi(k,n):return F(k*n,2*n*n-3*k*n+2*k*k)
mu=[(phi(k,2),F(1,k)) for k in range(1,3)]+[(phi(k,3),-F(1,k)) for k in range(1,4)]
stop=sum((c*max(v-F(1,2),0) for v,c in mu),F(0));assert stop==F(-1,24)
Path(__file__).with_name('identities.json').write_text(json.dumps({'partial_fraction_identity':True,'h1_symmetrized_second_derivatives':list(map(str,curv)),'normalized_phi_stop_loss_n2_cutoff_half':str(stop),'scope':'exact identities and shortcut falsifiers, no full theorem'},indent=2))
print('PASS exact identities and two route obstructions')
