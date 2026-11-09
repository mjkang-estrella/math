import pathlib,json,itertools,hashlib
from fractions import Fraction as F
import sympy as S
L=pathlib.Path(__file__).resolve().parent
x,y,z,w=S.symbols('x y z w');v=(x,y,z,w);s=sum(v);t=x+y+z
Q=x*(x+y)*t;P=x*x*t+x*y*s
U=[x*s*s,x*x*s+y*s*s,x**3+2*x*y*s+z*s*s]
cert=[]
for i,u in enumerate(U,1):
 d=S.Poly(u-P,*v);assert all(c>=0 for c in d.coeffs())
 cert.append(dict(n=i,candidate=str(S.expand(u-P)),bridge=str(S.expand(u-Q-2*x*y*w))))
 assert all(c>=0 for c in S.Poly(u-Q-2*x*y*w,*v).coeffs())
assert S.expand(P-Q-x*y*w)==0
xx,yy,zz=S.symbols('X Y Z')
p=(x*x*t+x*y).subs({x:xx,y:yy-xx,z:zz-yy},simultaneous=True).expand()
assert S.expand(p-(xx*yy+xx**2*(zz-1)))==0
assert [S.Poly(p.subs({yy:1,zz:1}),xx).total_degree(),S.Poly(p.subs(zz,1),xx,yy).total_degree(),S.Poly(p,xx,yy,zz).total_degree()]==[1,2,3]
points=0
for a in range(13):
 for b in range(13-a):
  for c in range(13-a-b):
   p0=[F(a,12),F(b,12),F(c,12),F(12-a-b-c,12)]
   X,Y,Z,W=p0;low=X*X*(X+Y+Z)+X*Y;better=X*(X+Y)*(X+Y+Z)+2*X*Y*W
   u=[F(1)]
   for n in range(1,33):
    u.append(sum(p0[j-1]*u[n-j] for j in range(1,min(n,4)+1)))
    assert u[n]>=better>=low
   points+=1
result=dict(status='PASS',grid_points=points,times=32,expansions=cert,subclass=str(p),proof_scope='identities exact; finite grid diagnostic only; universal proof in review.md')
(L/'check-results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
