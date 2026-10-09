"""Check only the significance reduction, not repeat the R2 proof audit."""
from pathlib import Path
import sys,json,hashlib,platform
ROOT=Path(__file__).resolve().parents[3]
vendor=ROOT/'frontier/experiments/i17_six_point_ramsey_r2/vendor'
deps=[]
for name in ['sympy-1.14.0-py3-none-any.whl','mpmath-1.3.0-py3-none-any.whl']:
    p=vendor/name;sys.path.insert(0,str(p));deps.append({'path':str(p.relative_to(ROOT)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size})
import sympy as s
t=s.symbols('t1:7');u=s.symbols('U1:7');x,y=s.symbols('x y');factors=[];vs=[];checks={}
for j,inds in enumerate([(0,1,2),(3,4,5)],1):
    M=s.Matrix([[t[i],1,-t[i]*u[i]] for i in inds]);D=s.expand(M.det());N=M.adjugate()*s.Matrix([u[i] for i in inds]);G=s.expand((N[2]*x+D)*y-N[0]*x-N[1]);V=s.prod(t[b]-t[a] for a,b in [(inds[0],inds[1]),(inds[0],inds[2]),(inds[1],inds[2])]);sub=dict(zip(u,t))
    checks[f'adjugate_{j}']=all(s.expand(z)==0 for z in M*N-D*s.Matrix([u[i] for i in inds]))
    checks[f'factor_vanish_{j}']=all(s.expand(G.subs({x:t[i],y:u[i]}))==0 for i in inds)
    checks[f'diagonal_{j}']=s.expand(G.subs(sub)-V*(y-x))==0
    checks[f'degree_{j}']=s.Poly(G,x,y).degree(x)<=1 and s.Poly(G,x,y).degree(y)<=1
    factors.append(G);vs.append(V)
Q=s.expand(factors[0]*factors[1]);V=s.expand(vs[0]*vs[1]);checks['six_evaluations']=all(s.expand(Q.subs({x:t[i],y:u[i]}))==0 for i in range(6));checks['product_diagonal']=s.expand(Q.subs(dict(zip(u,t)))-V*(y-x)**2)==0
checks['bidegree_2_2']=s.Poly(Q,x,y).degree(x)==s.Poly(Q,x,y).degree(y)==2
L=s.Matrix([[1,0,1],[1,0,-1],[0,2,0]]);J=s.Matrix([[0,0,1],[0,-2,0],[1,0,0]]);checks['circle_congruence']=L.T*s.diag(-1,1,1)*L==-2*J
assert all(checks.values())
out={'checks':checks,'status':'PASS','scope':'Universal polynomial verification over Q[t1,...,t6,U1,...,U6,x,y]; only left Vandermonde scalar inverted after choosing distinct field elements. Not a priority proof.','python':platform.python_version(),'sympy':s.__version__,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'dependencies':deps}
p=Path(__file__).with_name('reduction-check.json');p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
