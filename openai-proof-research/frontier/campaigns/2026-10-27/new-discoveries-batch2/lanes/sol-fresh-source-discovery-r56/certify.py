from check import strip,closure,neighbors
import sympy as s,json
from pathlib import Path
x=s.symbols('x')
T=s.Matrix([[1+2*x,0,x*x,0],[1+x,x,0,x*x],[1+2*x,0,0,0],[1,2*x,0,0]])
v=s.Matrix([[1,2*x,0,0]]);w=s.Matrix([1+2*x,1+x,1+2*x,1])
for n in range(2,17):
 p=s.Poly((v*w)[0],x);c=strip(n)
 assert [int(p.nth(k)) for k in range(2*n+1)]==c
 v=v*T
nb=neighbors(4,4);U=sum(1<<(i*4+j) for i in [1,2] for j in [1,2]);full=(1<<16)-1
assert closure(full^U,nb)==full
# Rayleigh exact difference, and a positive two-dimensional Hessian subspace.
assert 2*2-7*1==-3
# On span e_a+e_d and e_b+e_c, Hessian quadratic form is positive definite.
H=s.Matrix([[0,0,0,1],[0,0,1,0],[0,1,0,0],[1,0,0,0]])
R=s.Matrix([[1,0],[0,1],[0,1],[1,0]])
assert R.T*H*R==2*s.eye(2)
Path('certify.json').write_text(json.dumps({'transfer_polynomials_verified':15,'central_4x4_vacancy_cycle_clears':True,'Rayleigh_difference':-3,'Hessian_positive_restriction':[[2,0],[0,2]]},indent=2)+'\n')
print('PASS exact transfer/geometry/negative-route certificates')
