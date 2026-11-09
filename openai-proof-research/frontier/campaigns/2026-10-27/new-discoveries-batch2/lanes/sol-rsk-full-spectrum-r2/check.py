"""Targeted exact checks of a structural route, not range enumeration."""
from prior_check import *
from prior_spectral import plus_unipotent, square2
import sympy as S

def rec_case(s,p):
 ts,A=matrix(s,p);M=S.Matrix(A);t=S.Symbol('t');f=M.charpoly(t).as_expr();N=len(A)
 mod2=S.Poly(f,t,modulus=2).as_expr();g=S.Poly(f,t)
 for root in [1,-1]:
  while g.eval(root)==0:g=g.exquo(S.Poly(t-root,t))
 return {'s':s,'p':p,'N':N,'strict_interior':max(s)+max(p)<sum(s),'triangular':s[0]==p[0], 'charpoly':str(S.factor(f)),'charpoly_mod2':str(mod2),'mod2_unipotent':plus_unipotent(A),'non_pm1_factor_degree':g.degree(),'basis':ts,'matrix':A}

def main():
 # Specific symmetry-based targets; no enlarged rectangular range.
 out=[rec_case(s,p) for s,p in [((6,2),(2,2,2,2)),((5,3),(2,2,2,2)),((4,4),(2,2,2,2)),((4,2),(2,2,2))]]
 assert out[0]['mod2_unipotent'] and out[0]['non_pm1_factor_degree']==4
 # Actual source-normalized matrix satisfies the public predicted identity.
 A=S.Matrix(out[0]['matrix']);assert A**4==S.eye(10)
 assert str(S.factor(A.charpoly(S.Symbol('t')).as_expr()))=='(t - 1)**3*(t + 1)**3*(t**2 + 1)**2'
 (P/'checks.json').write_text(json.dumps({'status':'PASS','scope':'four targeted symmetry and neighboring-interior blocks only','cases':out},indent=2))
 print(json.dumps([{k:v for k,v in r.items() if k not in ['basis','matrix']} for r in out],indent=2))
if __name__=='__main__':main()
