import os,resource,json,itertools,time
from pathlib import Path
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import sys
sys.dont_write_bytecode=True
sys.path.append("/home/mj-kang/.local/lib/python3.14/site-packages")
import sympy as S
D=Path(__file__).resolve().parents[1];z,w,t,L,H,u=S.symbols('z w t L H u',nonzero=True)
# Leibniz expansion, deliberately no Matrix.det or inherited code.
def det(m):
 n=len(m);return S.expand(sum((-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))*S.prod(m[i][p[i]] for i in range(n)) for p in itertools.permutations(range(n))))
def graph(n,edges,ws):
 return [[(-w if i in ws else -z) if i==j else S.Integer(int(tuple(sorted((i,j))) in edges)) for j in range(n)] for i in range(n)]
edges={(0,1),(0,2),(0,3),(1,3),(2,4),(3,4)};m=graph(5,edges,{1,2});N=det([r[1:] for r in m[1:]]);Q=det(m);F=S.Poly(S.expand(t*(N-L*Q).subs({z:1/t,w:t*u})),u)
a,b,c=F.all_coeffs();delta=S.Poly(S.expand(b*b-4*a*c),t)
# Compute the radical as a formal series via convolution; select sqrt(delta)(0)=2L.
k=6;ds=[delta.nth(i) for i in range(k+1)];rs=[2*L]
for j in range(1,k+1):rs.append(S.factor((ds[j]-sum(rs[i]*rs[j-i] for i in range(1,j)))/(4*L)))
def divide(ns,den):
 out=[]
 for j in range(k):out.append(S.factor((ns[j]-sum(den[i]*out[j-i] for i in range(1,min(j,len(den)-1)+1)))/den[0]))
 return out
branches={}
for sign,name in [(-1,'slope1'),(1,'slope3')]:
 ns=[S.expand(-b).coeff(t,i)+sign*rs[i] for i in range(k)];co=divide(ns,[2*S.expand(a).coeff(t,i) for i in range(4)]);jet=sum(co[i]*t**(i+1) for i in range(k));branches[name]=co
 residual=S.Poly(S.expand(F.as_expr().subs(u,jet/t)),t)
 assert all(S.cancel(residual.nth(i))==0 for i in range(k))
 print(name,jet,flush=True)
 print('difference leading',S.factor(co[5 if sign==-1 else 1]-co[5 if sign==-1 else 1].subs(L,H)),flush=True)
print('N',S.factor(N),'Q',Q,'gcd',S.gcd(N,Q),'F',F.as_expr(),flush=True)
print('numerator factor tests',[S.factor(Q.subs(w,1/(z+e))) for e in [-1,1]],flush=True)
# Direct stable-denominator test: beta(f)=(Q+iN)/(Q-iN); L=-i makes N-LQ=0 equivalent to Q-iN=0.
# Use z=-1/x (not 1/x) for the upper-half-plane preserving chart.
x=S.symbols('x',real=True)
for name,co in branches.items():
 pole=S.expand(sum(v.subs(L,-S.I)*(-x)**(j+1) for j,v in enumerate(co)))
 print('pole jet',name,pole,'imaginary part',S.im(pole).expand(),flush=True)
# Source Example 4.3, read from its displayed Schur complement: two paths of lengths 2 and 3.
me=graph(5,{(0,2),(1,2),(0,3),(3,4),(1,4)},{1});ne=det([r[1:] for r in me[1:]]);qe=det(me)
assert S.cancel(ne/qe-(w*z**3-w*z-2*z**2+1)/(-w*z**4+3*w*z**2-w+2*z**3-4*z+2))==0
we=S.solve(ne-L*qe,w)[0];print('source Ex4.3',S.series(we.subs(z,1/t),t,0,7),flush=True)
# BH opening four-cycle example.
mb=graph(4,{(0,1),(1,2),(2,3),(0,3)},{3});nb=det([r[1:] for r in mb[1:]]);qb=det(mb)
assert S.cancel(nb/qb-(z+w-z*z*w)/(z**3*w-2*z*z-2*z*w))==0
print('BH example level',S.series(S.solve(nb-L*qb,w)[0].subs(z,1/t),t,0,7),flush=True)
(D/'logs/independent-results.json').write_text(json.dumps({'N':str(S.factor(N)),'Q':str(Q),'gcd':str(S.gcd(N,Q)),'F':str(F.as_expr()),'branches_w_coefficients':{n:list(map(str,co)) for n,co in branches.items()},'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss},indent=2))
print('ALL ASSERTIONS PASS; RSS KiB',resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)

R=S.expand(x**3*(Q-S.I*N).subs(z,-1/x))
print('stable denominator in x,w',R)
print('finite singularity resultant',S.factor(S.resultant(N,Q,w)))
print('common finite value N,Q',N.subs({z:S.Rational(1,2),w:-2}),Q.subs({z:S.Rational(1,2),w:-2}))
print('source calibration simplified', [S.factor(S.expand(S.series(we.subs(z,1/t),t,0,5).removeO()).coeff(t,j)) for j in range(1,5)])
