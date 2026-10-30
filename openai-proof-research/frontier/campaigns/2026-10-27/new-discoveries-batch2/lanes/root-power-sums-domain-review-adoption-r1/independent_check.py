from pathlib import Path
import itertools,json,datetime
import sympy as s
out=Path(__file__).parent
z=s.Symbol('z'); counts=[]
for h in [3,6,9,18,21,30]:
 phi=s.Poly(s.cyclotomic_poly(h,z),z);d=phi.degree()
 vec=[]
 for j in range(h):
  r=s.rem(s.Poly(z**(2*j),z),phi)
  vec.append(tuple(int(r.nth(k)) for k in range(d)))
 zero=(0,)*d;V=[zero]+vec;by_support={i:0 for i in range(1,5)}
 for first in range(4):
  for tail in itertools.product(range(h+1),repeat=3-first):
   ids=[1]+list(tail)
   if all(sum(V[i][k] for i in ids)==0 for k in range(d)):
    by_support[sum(i!=0 for i in ids)]+=1
 expected=8 if h%2 else 32
 assert sum(by_support.values())==expected and by_support[3]==expected
 counts.append(dict(h=h,b=h+2,support_counts=by_support,expected=expected))
w=s.Symbol('w');b=s.Symbol('b');x=s.Matrix([1,w,w*w,0]);v=s.Matrix([-w,1,0,0]);e=s.Matrix([0,0,0,1]);H=s.diag(*([b*(b-2)]*3+[-b]))
red=lambda a:s.rem(s.expand(a),w*w+w+1,w)
assert red((x.T*v)[0])==0 and red((x.T*x)[0])==0
G=s.Matrix([[red((a.T*H*c)[0]) for c in [v,e]] for a in [v,e]])
assert red(G.det()-b*b*(b-2)*w)==0
parts=0
for n in range(3,201):
 for c in range(n+1):
  for d in range(n+1):
   t=c+d
   if 0<t<2*n:
    I=n*t-2*c*d; assert I>=n
    if 2<=t<=2*n-2:assert I>=2*n-2
    parts+=1
res=[]
for n in range(3,501):
 normal=n%4!=2 and n%3!=2
 target=(n%6==5 and n>=11) or (n%12==8 and n>=20)
 excluded=n%4==2 or n in [5,8]
 assert sum([normal,target,excluded])==1
 res.append(n)
a=s.symbols('x1:5');p2=sum(t*t for t in a);p8=sum(t**8 for t in a);E=a[1]**2*a[2]**2+a[1]**2*a[3]**2+a[2]**2*a[3]**2-a[0]**4;Z=s.prod(a)
assert s.rem(p8-2*(E**2-2*Z**2),p2,a[0])==0
assert E.subs(dict(zip(a,[1,s.I,0,0])))==-1
p5=sum(t**5 for t in a)
assert s.groebner([sum(a),p2],*a).reduce(p5)[1]==0
vander=[]
for m in range(1,5):
 t=s.symbols('t:'+str(m));M=s.Matrix([[tj**k for tj in t] for k in range(m)])
 assert s.expand(M.det()-s.prod(t[j]-t[i] for i in range(m) for j in range(i+1,m)))==0
 vander.append(m)
r=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',exact_root_enumerations=counts,hessian_gram=str(G),hessian_det=str(red(G.det())),component_partitions=parts,residue_parameters=len(res),vandermonde_sizes=vander,b5_b8_identities=True,limits='Finite exact diagnostics only. Universal argument is in review.md; these computations are not a full proof.')
(out/'independent-evidence.json').write_text(json.dumps(r,indent=2));print(json.dumps(r))
