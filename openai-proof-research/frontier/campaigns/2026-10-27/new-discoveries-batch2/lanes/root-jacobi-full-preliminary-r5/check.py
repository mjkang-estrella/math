"""Root independent normal-form and linear-system diagnostics; finite only."""
import json
from pathlib import Path
from fractions import Fraction
from math import factorial
import sympy as S

a,b,x,u,v=S.symbols('a b x u v', real=True)
E=S.expand
def plus(p,q):return (E(p[0]+q[0]),E(p[1]+q[1]))
def neg(p):return (-p[0],-p[1])
def times(p,q):return (E(p[0]*q[0]+(1+x*x)*p[1]*q[1]),E(p[0]*q[1]+p[1]*q[0]))
def diff(p):return (E(-(1+x*x)*S.diff(p[0],x)),E(-x*p[1]-(1+x*x)*S.diff(p[1],x)))
def val(c):
    c=Fraction(c)
    if c==0:return 1000000
    z=lambda k:(abs(k)&-abs(k)).bit_length()-1
    return z(c.numerator)-z(c.denominator)
h=[(0,0),(a*(1+x*x),b*x)]
for n in range(1,9):
    q=neg(diff(h[n]))
    for j in range(1,n):q=plus(q,neg(times(h[j],h[n-j])))
    h.append(q)
src=json.loads((Path(__file__).parents[1]/'root-jacobi-adoption-r2/checks.json').read_text())
rows=[]
for n in range(1,10):
    A,B=h[n]
    for w,F in enumerate((A,B)):
        for (i,j,k),c in S.Poly(F,a,b,x).terms():
            if c==0:continue
            assert val(c)>=i.bit_count()+j.bit_count()-1
            assert j%2==w and (k+w)%2==(n+1)%2
    assert S.rem(A,1+x*x,x)==0
    if n%2==0:continue
    r=(n+1)//2
    # Solve the entire finite odd-unit operator as a rational linear system.
    deg=max(S.degree(B,x),1)-1
    co=S.symbols('c:'+str(int(deg//2)+1))
    f=sum(c*x**(2*k) for k,c in enumerate(co))
    equation=E(-x*f-(1+x*x)*S.diff(f,x)-B)
    sol=S.solve(S.Poly(equation,x).all_coeffs(),co,dict=True)[0]
    f=E(f.subs(sol));assert E(-x*f-(1+x*x)*S.diff(f,x)-B)==0
    midpoint=E(f.subs(x,0));J=0
    for (i,j),c in S.Poly(midpoint,a,b).terms():
        if c==0:continue
        d=i+j;assert val(c)>=(d-1).bit_count()
        J+=c*2**(n-d)*a**i*b**j
    J=E(J.subs({a:u+v,b:u-v}, simultaneous=True))
    source_im=S.sympify(src['rows'][n-1]['imaginary_part'],locals={'u':u,'v':v})
    assert E((-1)**r*factorial(n)*J-source_im)==0
    rows.append({'r':r,'J':str(S.factor(J)), 'midpoint_ab':str(S.factor(midpoint))})
# Check the exact rescaling and derivation under the Laurent embedding separately.
t=S.symbols('t',nonzero=True)
xx=(t-1/t)/2;ww=(t+1/t)/2;D=lambda f:-(1+t*t)*S.diff(f,t)
assert S.cancel(ww*ww-xx*xx-1)==0
assert S.cancel(D(xx)+2*ww*ww)==0
assert S.cancel(D(ww)+2*ww*xx)==0
assert S.cancel(u*(1+t*t)+v*(1+t**-2)-2*((u+v)*ww*ww+(u-v)*ww*xx))==0
out={'scope':'finite n<=9; independent symbolic pair ring and simultaneous linear solve',
     'status':'PASS','rows':rows}
Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: independent pair-ring/linear-system/source checks through n=9.')
