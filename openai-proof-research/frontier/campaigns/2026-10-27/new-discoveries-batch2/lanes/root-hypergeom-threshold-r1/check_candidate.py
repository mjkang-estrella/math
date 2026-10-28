"""Symbolic identities and high-precision diagnostics; not proof certificates."""
import json
from pathlib import Path
import sympy as S
import mpmath as M

a,b,r,H,w,T,c,d = S.symbols('a b r H w T c d', positive=True)
checks=[]
def zero(name, expr):
    assert S.factor(expr)==0, (name,S.factor(expr))
    checks.append(name)

cc=a+b; dd=a*b/cc
N=[S.rf(a,n)*S.rf(b,n)/(S.rf(cc+1,n)*S.factorial(n)) for n in range(3)]
D=[S.rf(a,n)*S.rf(b,n)/(S.rf(cc,n)*S.factorial(n)) for n in range(3)]
h1=S.factor(D[1]-N[1]); h2=S.factor(D[2]-N[2]-h1*N[1])
zero('h1',h1-dd/(cc+1))
zero('wprime0',2*h2-h1-a*b*(a*a+a+b*b+b)/(cc*(cc+1)**2*(cc+2)))
V=((d-w)*(T+1)-c*(2*H-1)*w)/T
Vboundary=S.factor(V.subs(H,w+S.Rational(1,2)).subs(T,c*(w*w-S.Rational(1,4))/(d-w)))
zero('z boundary derivative',Vboundary-(d-w)*(d-w-c*(w*w+S.Rational(1,4)))/(c*(w*w-S.Rational(1,4))))
# At w'=0, differentiate V along T'=T+1,H'=w,w'=0.
Vder=S.diff(V,T)*(T+1)+S.diff(V,H)*w
zero('wprime firstzero derivative', Vder-2*c*w*(H-w-S.Rational(1,2))/T + V/T)
zero('parameter threshold',dd/(cc+1)-a*(b-a)/cc-a*(a*(a+1)-b*b)/(cc*(cc+1)))
b1,b2=S.symbols('b1 b2',positive=True);c1=a+b1;c2=a+b2;d1=a*b1/c1;d2=a*b2/c2
zero('finite threshold',d2/(c2+1)-d2+a*a/c1-a*(a*(a+1)-b1*b2)/(c1*(c2+1)))
f1,f2=S.symbols('f1 f2');w2=S.symbols('w2')
rp1=c1*(1-f1)-d1*r*f1*f1/(1-r)
rp2=c2*(1-f2)-d2*r*f2*f2/(1-r)
lhs=rp1-rp2+(c1+d1*r*(f1+f2)/(1-r))*(f1-f2)
rhs=(b2-b1)*r*f2*f2/(c2*(1-r))*(w2-d2+a*a/c1)
zero('comparison ODE', (lhs-rhs).subs(w2,d2-c2*(1/f2)*(1/f2-1)*(1-r)/r))
zero('specialization',(a*(a+1)-(1-a)*(S.Rational(3,2)-a))-(7*a-3)/2)

M.mp.dps=55
rows=[]
for aa in ['.001','.02','.1','.5','1','2','10','100']:
 for bb in ['.001','.02','.1','.5','1','2','10','100']:
  av,bv=M.mpf(aa),M.mpf(bb);cv=av+bv;dv=av*bv/cv
  for rr in ['.001','.05','.3','.7','.95','.999']:
   rv=M.mpf(rr);hv=M.hyp2f1(av,bv,cv,rv)/M.hyp2f1(av,bv,cv+1,rv)
   tv=rv/(1-rv);wv=dv-cv*hv*(hv-1)/tv
   wp=((dv-wv)*(tv+1)-cv*(2*hv-1)*wv)/tv
   zv=hv-wv-M.mpf('.5')
   assert min(wv,wp,zv)>0,(aa,bb,rr,wv,wp,zv)
   rows.append({'a':aa,'b':bb,'r':rr,'wprime':M.nstr(wp,35),'z':M.nstr(zv,35)})
result={'symbolic_checks':checks,'transformed_ODE_diagnostics':len(rows),
        'warning':'Numerical diagnostics are not rigorous interval certificates or proofs.','rows':rows}
Path(__file__).with_name('checks.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS',len(checks),'symbolic identities;',len(rows),'numerical ODE diagnostics')
