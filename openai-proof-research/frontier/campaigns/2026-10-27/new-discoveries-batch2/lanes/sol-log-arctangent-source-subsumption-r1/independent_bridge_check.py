"""Independent exact bridge/obstruction checker; NOT the finite+tail certificate.
Run under 512MiB RLIMIT_AS, 15s RLIMIT_CPU. No floating arithmetic.
"""
import os,resource,json
from fractions import Fraction as F
from pathlib import Path
for k in ['OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912))
resource.setrlimit(resource.RLIMIT_CPU,(15,15))
class Q:
 def __init__(self,a=0,b=0):self.a,self.b=F(a),F(b)
 def __add__(x,y):
  y=y if isinstance(y,Q) else Q(y);return Q(x.a+y.a,x.b+y.b)
 __radd__=__add__
 def __neg__(x):return Q(-x.a,-x.b)
 def __sub__(x,y):return x+-y if isinstance(y,Q) else x+Q(-y)
 def __mul__(x,y):
  y=y if isinstance(y,Q) else Q(y);return Q(x.a*y.a+17*x.b*y.b,x.a*y.b+x.b*y.a)
 __rmul__=__mul__
 def __truediv__(x,y):
  y=y if isinstance(y,Q) else Q(y);z=y.a*y.a-17*y.b*y.b;assert z;return x*Q(y.a/z,-y.b/z)
 def eq(x,y):return x.a==y.a and x.b==y.b
 def sign(x):
  a,b=x.a,x.b
  if b==0:return (a>0)-(a<0)
  if a==0:return (b>0)-(b<0)
  if a*b>0:return (a>0)-(a<0)
  z=a*a-17*b*b
  return ((a>0)-(a<0))*((z>0)-(z<0))
 def out(x):return [str(x.a),str(x.b)]
d=Q(0,1);alpha=(Q(5)+d)/2;beta=(Q(5)-d)/2
assert (alpha+beta).eq(Q(5)) and (alpha*beta).eq(Q(2))
# Formal even series division: Mcenter=(sinh(t)/t)/(atan(sqrt2*t)/(sqrt2*t)).
a=[F(1),F(1,6),F(1,120),F(1,5040)];b=[F(1),F(-2,3),F(4,5),F(-8,7)];c=[]
for n in range(4):c.append(a[n]-sum(b[j]*c[n-j] for j in range(1,n+1)))
g2=c[1];g4=c[2]-c[1]*c[1]/2;assert g2==F(5,6)
g6=c[3]-c[1]*c[2]+c[1]**3/3
# Any real Stolarsky representation has log coefficients (r+s)/6 and
# -(r+s)(r*r+s*s)/180. Matching g2,g4 forces r+s=5, rs=2.
s6=F(437,567)
assert s6!=g6
rows=[]
for p,q in [(d,beta),(-d,alpha)]:
 assert (p+q+q).eq(Q(5));assert (p+q).eq(alpha if p.sign()>0 else beta)
 # coefficient of t² in log Fp(e^-t,e^t), Fp=M(x^(1/p),y^(1/p))^p
 f2=Q(g2)/p;r=q/p
 assert (f2-Q(F(1,2))).sign()<0 # first branch contradicts Thm4.4's A<Fp
 sandwich_gap=f2-(Q(1)+r)/4
 if p.sign()<0:assert sandwich_gap.sign()<0 # contradicts Thm4.2's sandwich<=Fp
 rows.append({'p':p.out(),'q':q.out(),'r=q/p':r.out(),'Fp_minus_A_t2':(f2-Q(F(1,2))).out(),'Fp_minus_sandwich_t2':sandwich_gap.out()})
# Symbolic cancellation after common midpoint q-denominator: coefficient vector in X,Y,Z.
left=[F(-2),F(2),F(0)];right=[F(0),F(-2),F(2)];whole=[F(-2),F(0),F(2)]
assert [x+y for x,y in zip(left,right)]==whole
# Exact falsifier of the abstract implication [z<S and R<S] => z<R.
assert F(1)<F(3) and F(2)<F(3) and not F(2)<F(1)
out={'scope':'exact local conjugation obstructions and classical telescoping algebra only; no global derivative or Lean certificate','status':'PASS_SCOPED','g_t2':str(g2),'g_t4':str(g4),'g_t6':str(g6),'S_t6':str(s6),'S_minus_M_t6':str(s6-g6),'branches':rows,'telescoping_symbolic_coefficients':list(map(str,whole)),'limits':{'AS':536870912,'CPU':15,'threads':1}}
Path(__file__).with_name('independent-bridge-evidence.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
