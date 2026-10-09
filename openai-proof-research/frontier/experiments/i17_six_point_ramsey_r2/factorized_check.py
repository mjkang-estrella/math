"""Independent universal polynomial certificate from two three-point factors.
This is a simplification, not a repair of I17's valid residual proof.
"""
from pathlib import Path
import sys,json
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
for wheel in (HERE/'vendor').glob('*.whl'):sys.path.insert(0,str(wheel))
import sympy as s
x,y=s.symbols('x y');T=s.symbols('t1:7');U=s.symbols('U1:7');records=[];G=[];V=[]
for idx in [(0,1,2),(3,4,5)]:
 M=s.Matrix([[T[i],1,-T[i]*U[i]] for i in idx]);det=s.expand(M.det());n=M.adjugate()*s.Matrix([U[i] for i in idx]);g=s.expand((n[2]*x+det)*y-n[0]*x-n[1]);v=s.prod(T[j]-T[i] for ix,i in enumerate(idx) for j in idx[ix+1:]);diag=dict(zip(U,T))
 assert s.expand(det.subs(diag)-v)==0
 for i in idx:assert s.expand(g.subs({x:T[i],y:U[i]}))==0
 assert s.expand(g.subs(diag)-v*(y-x))==0
 assert s.degree(g,x)<=1 and s.degree(g,y)<=1
 G.append(g);V.append(v)
 records.append({'indices':[i+1 for i in idx],'D':str(det),'V':str(v),'G':str(g),'evaluations_checked':3,'diagonal':'V*(y-x)'})
E=s.Poly(G[0]*G[1],x,y)
assert E.degree(x)<=2 and E.degree(y)<=2
# Full expanded checks also certify the product, not only its factors.
for i in range(6):assert s.expand(E.as_expr().subs({x:T[i],y:U[i]}))==0
assert s.expand(E.as_expr().subs(dict(zip(U,T)))-V[0]*V[1]*(y-x)**2)==0
out={'status':'PASS','sympy_version':s.__version__,'formal_variables':[str(v) for v in T+U],'triples':records,'product_bidegree':[E.degree(x),E.degree(y)],'product_tensor_normalizer':'(V123*V456)^(-1) tensor 1','product_evaluations_checked':6,'diagonal_product_checked':True,'coefficient_order':[[i,j] for i in range(3) for j in range(3)],'polynomial_product_coefficients':[str(s.factor(E.coeff_monomial(x**i*y**j))) for i in range(3) for j in range(3)],'logical_scope':'Universal polynomial identities over Q[T,U]; distinctness makes the normalization nonzero. No finite jets or numeric parameter substitutions.'}
(HERE/'factorized-check.json').write_text(json.dumps(out,indent=2)+'\n');print('PASS: six factor evaluations, six product evaluations and diagonal product, all 12 formal variables')
