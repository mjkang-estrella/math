from fractions import Fraction as F
from pathlib import Path
import math,json
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r220')
def mat(x):return [[F(t) for t in row] for row in x]
def add(A,B):return [[a+b for a,b in zip(x,y)] for x,y in zip(A,B)]
def neg(A):return [[-a for a in row] for row in A]
def scale(c,A):return [[c*a for a in row] for row in A]
def tr(A):return [list(x) for x in zip(*A)]
def mul(A,B):return [[sum(a*b for a,b in zip(row,col)) for col in zip(*B)] for row in A]
def inv(A):
 a,b=A[0];c,d=A[1];return scale(1/(a*d-b*c),[[d,-b],[-c,a]])
H=[mat([[2,1],[1,2]]),mat([[3,0],[0,1]])];C=[mat([[1,2],[0,1]]),mat([[2,0],[1,3]])];S=[mat([[1,0],[0,2]]),mat([[2,0],[0,1]])]
L=[mul(C[i],inv(H[i])) for i in range(2)];V=[add(S[i],mul(mul(L[i],H[i]),tr(L[i]))) for i in range(2)]
avg=lambda x:scale(F(1,2),add(*x))
Q=add(avg(V),neg(mul(mul(avg(C),inv(avg(H))),tr(avg(C)))))
Lb=mul(avg(C),inv(avg(H)));U=[add(l,neg(Lb)) for l in L]
res=avg([mul(mul(U[i],H[i]),tr(U[i])) for i in range(2)])
assert add(Q,neg(avg(S)))==res
assert res[0][0]>0 and res[1][1]>0 and res[0][0]*res[1][1]-res[0][1]**2>=0
out={'purpose':'Author sanity calculations only; neither mathematical review nor artifact acceptance gate','noncommuting_covariance_exact':[[str(x) for x in row] for row in res],'quadrature':[]}
for N in (120,240):
 t=[(i+.5)*math.pi/N for i in range(N)]
 for eps in (0.,.001,.002):
  psi=[x+eps*math.sin(4*x)**3 for x in t];dp=[1+12*eps*math.sin(4*x)**2*math.cos(4*x) for x in t]
  val=0.
  for i in range(N):
   for j in range(i+1,N):
    z=t[j]-t[i];zz=psi[j]-psi[i]
    w=math.sin(z)**2*abs(math.sin(2*z)/2)
    f=math.sin(zz)**2*abs(math.sin(2*zz)/2)/(dp[i]*dp[j])**1.5
    val+=2*(f-w)
  delta=val*(math.pi/N)**2
  out['quadrature'].append(dict(N=N,epsilon=eps,Delta_midpoint=delta,Delta_over_epsilon_squared=delta/eps**2 if eps else None))
(R/'private/math-sanity.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
