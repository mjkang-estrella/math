"""Exact targeted checks; no tree-rank survey and no source proof."""
import os
for name in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):
    os.environ[name]='1'
import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(40,40))
import sympy as s
import json
from pathlib import Path
x,t=s.symbols('x t')
T=((None,(None,None)),((None,None),None))
z=s.symbols('z0:6')
def build(T,it):
    return next(it) if T is None else build(T[0],it)**2+build(T[1],it)**3
def depths(T,L=0,R=0):
    return [(L,R)] if T is None else depths(T[0],L+1,R)+depths(T[1],L,R+1)
def mod(p): return s.Poly(p,x,modulus=2).as_expr()
def val(n,p):
    n=abs(int(n)); k=0
    while n%p==0: n//=p;k+=1
    return k
def signatures(T):
    if T is None: return x,[(0,s.Integer(1))]
    a,aa=signatures(T[0]);b,bb=signatures(T[1])
    return mod(a*a+b**3),[(L+1,mod(k*k)) for L,k in aa]+[(L,mod(b*b*k)) for L,k in bb]
P=s.Poly(build(T,iter(z)),*z)
diag={v:x for v in z}; rows=[]
for i,(L,R) in enumerate(depths(T)):
    w=s.Poly(P.diff(z[i]).as_expr().subs(diag),x)
    assert min(val(c,2) for c in w.all_coeffs() if c)==L
    assert min(val(c,3) for c in w.all_coeffs() if c)==R
    h=mod(w.as_expr()/2**L)
    rows.append({'i':i,'L':L,'R':R,'h':str(h)})
# Independent literal partial derivatives with repeated labels in both characteristics.
u,v=s.symbols('u v')
Q=build(T,iter([u,v,u,v,u,v]))
for p,extreme in [(2,v),(3,u)]:
    for label in [u,v]:
        d=s.Poly(s.diff(Q,label),u,v,modulus=p)
        assert d.is_zero == (label != extreme)
# Literal single-leaf Hasse coefficients from independent variables.
p,ks=signatures(T)
for i,(L,k) in enumerate(ks):
    E=s.Poly(P.as_expr().subs({v:x+(t if j==i else 0) for j,v in enumerate(z)}),t)
    assert all(mod(E.nth(j))==0 for j in range(1,2**L))
    assert mod(E.nth(2**L))==k
    rows[i]['hasse']=str(k)
# Two masks agree at every L=0 leaf; first difference is at L=1.
c=[0]*6; d=[0]*6; d[2]=d[4]=1
C=build(T,iter([x+t*a for a in c]));D=build(T,iter([x+t*a for a in d]))
E=s.Poly(D-C,t)
assert mod(E.nth(1))==0
assert mod(E.nth(2))==mod(ks[2][1]+ks[4][1])==x**10
assert s.degree(ks[2][1],x)==s.degree(ks[4][1],x)==16
assert mod(s.sympify(rows[2]['h'])+s.sympify(rows[4]['h']))==x**11+x**8
h0=s.Poly(s.sympify(rows[0]['h']),x)
hasse3=mod(sum(c*s.binomial(m[0],3)*x**(m[0]-3) for m,c in h0.terms() if m[0]>=3))
assert hasse3==x**4+1 and ks[0][1]==1
out={'higher_hasse_shortcut':{'D3_h_leaf0':str(hasse3),'K_leaf0':str(ks[0][1])},'status':'PASS','tree':'F(F(x,F(x,x)),F(F(x,x),x))','rows':rows,
 'two_mask_difference_t2_mod2':'x**10','hasse_same_leading_degree':16,
 'memory_bytes':512*1024**2,'cpu_seconds':40,'blas_threads':1,
 'scope':'Exact targeted identities only; no source isolation, all-order independence or counterexample'}
Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
