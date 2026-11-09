from pathlib import Path
import sympy as S,json,datetime
pdir=Path(__file__).resolve().parents[1];q=S.Symbol('q');rows=[]
for n in [4,7,13,16]:
 l,s=divmod(n,9);t1,t2=(7,5) if s==4 else (4,8)
 M=S.Poly(S.cyclotomic_poly(n,q)**2,q,domain=S.QQ)
 def mon(e):
  return S.Poly(q**e,q,domain=S.QQ).rem(M) if e>=0 else S.invert(S.Poly(q**(-e),q,domain=S.QQ),M)
 one=mon(0)
 for c in [-t1,t2]:
  term=one;total=term
  for k in range(1,n):
   num=mon(9)
   for e in [1+c*n+9*(k-1),2-c*n+9*(k-1),6+9*(k-1)]:num=(num*(one-mon(e))).rem(M)
   den=(one-mon(9*k))**3
   term=(term*num*S.invert(den.rem(M),M)).rem(M);total=(total+term).rem(M)
  assert total.is_zero
  rows.append(dict(n=n,c=c,exact_deformation_mod_Phi_squared=True))
# Validate all linear table inequalities symbolically via constant and slope.
l=S.Symbol('l',nonnegative=True,integer=True)
for n,t1,t2,L1,L2,J3,J7,J8 in [(9*l+4,7,5,7*l+3,5*l+2,3*l+1,4*l+1,2*l),(9*l+7,4,8,4*l+3,8*l+6,3*l+2,l,5*l+3)]:
 for expr in [n-L1,n-L2,L1-J3,L1-J7,L2-J3,L2-J8]:
  z=S.Poly(expr,l);assert z.nth(0)>0 and z.nth(1)>=0
 for a,J in [(3,J3),(7,J7),(8,J8)]:assert S.cancel((a+9*J)/n).is_Integer
 assert S.expand(9*L1+1-t1*n)==0 and S.expand(9*L2+2-t2*n)==0
result=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),rows=rows,all_l_linear_index_bounds=True,limit='Exact finite deformations plus symbolic index-table checks; full proof remains in pivot-proof.md.')
(pdir/'checks/pivot-results.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
