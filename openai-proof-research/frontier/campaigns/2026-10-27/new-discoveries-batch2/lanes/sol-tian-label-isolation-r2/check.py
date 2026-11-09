#!/usr/bin/env python3
"""Bounded exact checks of prescribed identities, not a tree/rank survey."""
import os, resource
for key in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'): os.environ[key]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(40,40))
import sympy as s, json
from pathlib import Path
x=s.Symbol('x'); out={}
def ev(t):
 if t is None:return s.Poly(x,x),[s.Poly(1,x)]
 a,wa=ev(t[0]);b,wb=ev(t[1])
 return a*a+b**3,[2*a*w for w in wa]+[3*b*b*w for w in wb]
def order(p):return min(m[0] for m,c in p.terms() if c)
def envelope(a,b):
 g=s.gcd(a,b*b); ma,mb=order(a),order(b);h0,h1=order(g),g.degree();d,e=a.degree(),b.degree()
 lo=max(0,ma-1-2*mb+h0,mb-1-ma+h0)
 hi=min(d-1-2*e+h1,e-1-d+h1)
 return dict(degrees=[d,e],orders=[ma,mb],gcd_degree=h1,gcd_order=h0,H_min_order=lo,H_max_degree=hi,separates=lo>hi)
q=(None,None);A=(q,q);B=(q,None);T=(A,B)
a,wa=ev(A);b,wb=ev(B);p,w=ev(T)
base=envelope(a,b);assert base['separates'];out['base']=base
# Confirm the strengthened argument at every internal node of the base tree.
def certify(t):
 if t is None:return True
 aa,_=ev(t[0]);bb,_=ev(t[1]);return envelope(aa,bb)['separates'] and certify(t[0]) and certify(t[1])
assert certify(T)
# Weighted Euler identity, an all-order algebraic formula checked on this tree.
def weights(t,v=1):
 if t is None:return [v]
 return weights(t[0],2*v)+weights(t[1],3*v)
assert (sum((s.Rational(1,v)*x*z for v,z in zip(weights(T),w)),s.Poly(0,x))-p).is_zero
# Prescribed substitution U=B^(2), not an exhaustive or random rank survey.
U=(None,q);u,wu=ev(U)
def subst(t):return U if t is None else (subst(t[0]),subst(t[1]))
aa,_=ev(subst(A));bb,_=ev(subst(B));pp,ww=ev(subst(T));ext=envelope(aa,bb)
assert not ext['separates'];assert ext['H_min_order']==5 and ext['H_max_degree']==8
assert s.gcd(aa,bb*bb)==u**4
# Witness for the INTERVAL ENVELOPES, not for the actual gradient spaces.
h=s.Poly(x**5,x);g=u**4;left=(bb*bb).exquo(g)*h;right=aa.exquo(g)*h
assert aa*left==bb*bb*right
for z,child in [(left,aa),(right,bb)]:
 assert order(z)>=order(child)-1 and z.degree()<=child.degree()-1
out['substitution_envelope_failure']=dict(ext,U=str(u.as_expr()),H='x^5',left_order=order(left),left_degree=left.degree(),right_order=order(right),right_degree=right.degree(),actual_dependence=False)
# Chain rule factors: grouping follows outer-leaf then inner-leaf order.
factors=[s.Poly(z.as_expr().subs(x,u.as_expr()),x)*v for z in w for v in wu]
assert factors==ww
assert pp==s.Poly(p.as_expr().subs(x,u.as_expr()),x)
out['substitution_chain_rule']=dict(leaves=len(ww),degree=pp.degree(),verified=True,rank_survey=False)
# Coefficient-space injection for inner U: fixed independent minor suffices.
M=s.Matrix([[z.nth(k) for z in wu] for k in [1,5,6]])
# Select fixed rows from the explicit comb gradients, no search.
if M.det()==0:
 M=s.Matrix([[z.nth(k) for z in wu] for k in [1,5,7]])
assert M.det()!=0
out['inner_fixed_minor']=str(M.det())
# Verify the recurrence for the first two binary-color perturbation jets.
# Choose one fixed pair of masks with differing repeated labels.
t=s.Symbol('t')
def jet(tree,mask,index):
 if tree is None:
  v=(s.Poly(x,x),s.Poly(mask[index[0]],x),s.Poly(0,x));index[0]+=1;return v
 a=jet(tree[0],mask,index);b=jet(tree[1],mask,index)
 return (a[0]**2+b[0]**3,2*a[0]*a[1]+3*b[0]**2*b[1],a[1]**2+2*a[0]*a[2]+3*b[0]**2*b[2]+3*b[0]*b[1]**2)
mask=[1,0,1,0,0,1,0];j=jet(T,mask,[0]);assert j[1]==sum((v*z for v,z in zip(mask,w)),s.Poly(0,x))
# Independently evaluate the bivariate polynomial and compare Taylor coefficients.
def colored(tree,index):
 if tree is None:
  v=x+t*mask[index[0]];index[0]+=1;return s.Poly(v,t,x)
 l=colored(tree[0],index);r=colored(tree[1],index);return l*l+r**3
cp=colored(T,[0]);expr=cp.as_expr()
for k in range(3):assert s.Poly(expr.coeff(t,k),x)==j[k]
out['binary_jet_recurrence']={'orders_verified':[0,1,2],'mask':mask,'not_a_labeling_survey':True}
# A common nonzero root does not imply a common q-composition, even
# for individually isolated combs; the order gives an exact obstruction.
qp=s.Poly(x*x+x**3,x);bp=qp*qp+s.Poly(x**3,x);cp=bp*bp+s.Poly(x**3,x)
assert s.gcd(qp,cp)==qp and order(cp)==3
out['common_root_not_uniform_substitution']={'gcd':'x^2+x^3','C_order':3,'q_order':2,'C_not_in_Q_q':'every nonzero h(q) with h(0)=0 has even order','both_isolated':'source Propositions 6/7; root F(q,C) isolated by Proposition 9'}
out['limits']={'address_space_bytes':512*1024**2,'cpu_seconds':40,'blas_threads':1,'no_lean':True}
Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
