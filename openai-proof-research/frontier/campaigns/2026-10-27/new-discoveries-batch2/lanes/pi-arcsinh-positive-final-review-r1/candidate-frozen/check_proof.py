"""Independent exact derivative identification plus high-precision diagnostics.
The quantified proof is PROOF.md, not these finite checks.
"""
import json
import sympy as S
import mpmath as M
p,a,u = S.symbols("p a u", positive=True)
f=S.exp(-S.log(1+S.exp(-a*p))/p)
v=S.exp(-a*p)
H=S.log(1+v)-v*S.log(v)/(1+v)
formula=f/p**4*(H**2-2*p*H-p**3*a**2*v/(1+v)**2)
assert S.simplify((S.diff(f,p,2)-formula)/f)==0
h=S.log(1+u)-u*S.log(u)/(1+u)
assert S.simplify(S.diff(h,u)+S.log(u)/(1+u)**2)==0
r=u/(1+u)
assert S.simplify(S.expand_log(h+r*S.log(r)+(1-r)*S.log(1-r),force=True))==0
M.mp.dps=60
count=0
for pp in [M.log(2)/2+M.mpf(".0001"),M.mpf(".35"),M.mpf(".5"),1,2,4]:
 for tt in [M.mpf("1e-8"),M.mpf(".1"),M.mpf(".9"),1,2,100]:
  pp=M.mpf(pp); tt=M.mpf(tt)
  ff=lambda q:(1+tt**q)**(-1/q)
  actual=M.diff(ff,pp,2)
  v=tt**pp
  hh=M.log1p(v)-v*M.log(v)/(1+v)
  rhs=ff(pp)/pp**4*(hh**2-2*pp*hh-pp**3*M.log(tt)**2*v/(1+v)**2)
  assert actual<0
  assert M.almosteq(actual,rhs,rel_eps=M.mpf("1e-40"),abs_eps=M.mpf("1e-55")), (pp,tt,actual,rhs,actual-rhs)
  count+=1
# Direct quadrature of actual Jensen gaps, independent of differentiation.
min_gap=M.inf
for xx in [M.mpf(".0001"),M.mpf(".1"),M.mpf(".9"),1,2,10]:
 for p0,p1 in [(M.mpf(".35"),M.mpf(".8")),(1,2),(2,5)]:
  p0=M.mpf(p0);p1=M.mpf(p1)
  A=lambda pp:M.quad(lambda t:(1+t**pp)**(-1/pp),[0,xx])
  gap=A((p0+p1)/2)-(A(p0)+A(p1))/2
  assert gap>0
  min_gap=min(min_gap,gap)
print(json.dumps({"exact_symbolic_identities":3,"direct_second_derivative_diagnostics":count,"actual_integral_midpoint_diagnostics":18,"minimum_midpoint_gap":str(min_gap),"not_a_proof_of_universal_claim":True},indent=2))
