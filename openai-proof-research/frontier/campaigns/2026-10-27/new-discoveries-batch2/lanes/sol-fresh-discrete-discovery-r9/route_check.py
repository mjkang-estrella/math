from check import *

def main():
 s=(2,2);p=(1,2,1);pp=(2,2,1);witness=None
 for a in tables(s,p):
  a2=(a[0]+1,)+a[1:]
  f=expand(*literal(a,p),3);rhs={(x[0]+1,)+x[1:]:v for x,v in f.items()};lhs=expand(*literal(a2,pp),3)
  diff={x:lhs.get(x,0)-rhs.get(x,0) for x in set(lhs)|set(rhs)};diff={x:v for x,v in diff.items() if v}
  if diff:witness={'row_one':a,'row_two':tuple(y-x for x,y in zip(a,p)),'difference_terms_row_one_exponent_and_coefficient':list(diff.items())};break
 assert witness
 import sympy as S
 t=S.Symbol('t');s=(5,5);p=(4,4,2);ts,A=matrix(s,p);A2=mul(A,A);A4=mul(A2,A2)
 assert len(A)==13 and tr(A2)==13 and tr(A4)==85
 f=S.Matrix(A).charpoly(t).as_expr();expected=(t-1)**3*(t+1)**2*(t**3+3*t*t-1)*(t**5+t**4+t**3+2*t*t-t-1)
 assert S.expand(f-expected)==0
 # General 3x3 implementation cross-checks actual source Table5.
 from general_check import contingencies,general_literal,general_expand
 ts3=list(contingencies((1,1,1),(1,1,1)));idx={x:i for i,x in enumerate(ts3)};B=[[0]*len(ts3) for _ in ts3]
 for k,a in enumerate(ts3):
  for b,v in general_expand(*general_literal(a)).items():B[idx[b]][k]=v
 assert S.expand(S.Matrix(B).charpoly(t).as_expr()-(t-1)*(t+1)**2*(t**3+2*t*t+1))==0
 out={'status':'PASS','multiplication_noncommutation':witness,'second_moment_obstruction':{'s':s,'p':p,'N':13,'tr2':13,'tr4':85,'charpoly':str(expected),'basis':ts,'matrix':A},'source_Table5_crosscheck':'PASS'}
 (P/'route-checks.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:v for k,v in out.items() if k!='second_moment_obstruction'},indent=2))
if __name__=='__main__':main()
