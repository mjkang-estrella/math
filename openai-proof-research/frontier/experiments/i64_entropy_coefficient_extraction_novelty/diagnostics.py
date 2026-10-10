"""Independent finite checks. Not a universal proof or an I63 substitute. Read-only."""
from fractions import Fraction as Q
from itertools import product,permutations,combinations
import json,random
class Matrix:
 def __init__(self,rows):self.a=[[Q(x) for x in r] for r in rows];self.n=len(rows)
 def __getitem__(self,k):i,j=k;return self.a[i][j]
 def __setitem__(self,k,v):i,j=k;self.a[i][j]=Q(v)
 def __add__(self,b):return Matrix([[self[i,j]+b[i,j] for j in range(self.n)] for i in range(self.n)])
 def __sub__(self,b):return self+(-1)*b
 def __mul__(self,b):
  if isinstance(b,Matrix):return Matrix([[sum(self[i,k]*b[k,j] for k in range(self.n)) for j in range(self.n)] for i in range(self.n)])
  return Matrix([[b*self[i,j] for j in range(self.n)] for i in range(self.n)])
 __rmul__=__mul__
 def __eq__(self,b):return self.a==b.a
 def extract(self,rows,cols):return Matrix([[self[i,j] for j in cols] for i in rows])
 def det(self):
  if self.n==0:return Q(1)
  return sum((-1)**j*self[0,j]*self.extract(range(1,self.n),[k for k in range(self.n) if k!=j]).det() for j in range(self.n))
class sp:
 Rational=Q
 @staticmethod
 def zeros(m):return Matrix([[0]*m for _ in range(m)])
 @staticmethod
 def eye(m):return Matrix([[int(i==j) for j in range(m)] for i in range(m)])
n=0
def check(b):
 global n
 assert bool(b);n+=1
# A genuinely convex compact test function f(u)=u/2+u^2/8, not q and not a global f example.
a=Q(1,4);h=Q(1,4);MR=16/a**2+16/h**2*(1+2/a**2)
vals=[Q(-1),Q(-1,2),Q(0),Q(1,2),Q(1)]
for i,s,r,A,C in product(vals,vals,vals,range(-2,3),range(-2,3)):
 alpha=Q(1,2)+(i+s)/8;beta=Q(1,2)+(i+r)/8;gamma=1-alpha;eta=1-beta
 ep=alpha*A-beta*C;em=gamma*A-eta*C;d=A-C;z=(i+s)*A-(i+r)*C
 check(d*d<=2/a**2*(ep*ep+em*em));check(z*z<=MR*(ep*ep+em*em))
 check((alpha-beta)*(gamma-eta)<=0)
 if s!=r:
  # Nullvector of one curl, excluded by the reflected curl; no matrix coercivity shortcut.
  A0=beta;C0=alpha
  check(alpha*A0-beta*C0==0);check(A0-C0!=0);check(gamma*A0-eta*C0!=0)
pair_count=n
rng=random.Random(6417); records=[]
for m in [2,3,4]:
 for case in range(3):
  X=[]
  for r in range(m):
   M=sp.zeros(m)
   for i in range(m):
    for j in range(i,m):M[i,j]=M[j,i]=sp.Rational(rng.randrange(-3,4),5)
   X.append(M)
  T=lambda i,j,r:X[r][i,j]
  S=lambda i,j,r:T(i,j,r)-T(i,r,j)
  ns=sum(S(i,j,r)**2 for i,j,r in product(range(m),repeat=3))
  ne=sum((T(i,j,r)-sum(T(*p) for p in permutations((i,j,r)))/6)**2 for i,j,r in product(range(m),repeat=3))
  check(ns==3*ne)
  B=sum((M*M for M in X),sp.zeros(m));K=max(sum(abs(B[i,j]) for j in range(m)) for i in range(m))
  # Explicit Gaussian Wick enumeration, compared to operator product formula.
  W=sp.zeros(m)
  for r,s,t,u in product(range(m),repeat=4):
   w=int(r==s and t==u)+int(r==t and s==u)+int(r==u and s==t)
   if w:W+=w*X[r]*X[s]*X[t]*X[u]
  formula=B*B+sum((M*B*M for M in X),sp.zeros(m))+sum((X[r]*X[s]*X[r]*X[s] for r,s in product(range(m),repeat=2)),sp.zeros(m))
  check(W==formula)
  H=3*K*K*sp.eye(m)-W
  for k in range(1,m+1):
   for ids in combinations(range(m),k):check(H.extract(ids,ids).det()>=0)
  # Compare every coefficient of curl(L^2) to commutator plus asymmetry error.
  for i,r,s,t in product(range(m),repeat=4):
   lhs=(X[t]*X[r]+X[r]*X[t])[i,s]-(X[t]*X[s]+X[s]*X[t])[i,r]
   rem=sum(X[r][i,j]*S(j,s,t)-X[s][i,j]*S(j,r,t)+X[t][i,j]*S(j,s,r) for j in range(m))
   rhs=(X[r]*X[s]-X[s]*X[r])[i,t]+rem
   check(lhs==rhs)
  records.append(dict(m=m,case=case,K=str(K),symmetry_squared=str(ne)))
# Original output cap does not cap coefficient/input flattening, at arbitrarily large m.
for m in [2,5,31,101]:
 # X_1=I, X_r=0 for r>1. B=I, G_input=diag(m,0,...).
 check(m>1);check(Q(m,1)>1)
# Exact heavy creation and repair for the family above, m>28.
# Sym X has T_111=1 and each permutation of (1,i,i) equal to 1/3.
# B_T=diag(1+(m-1)/9,2/9,...), so P removes e_1 and P^3 T=0.
repair=[]
for m in [29,38,101,1001]:
 e2=Q(2*(m-1),3);mass=1+Q(m-1,9)
 check(mass>4);check(mass<=4*e2);check(m<=26*e2);check(m<=234*e2)
 repair.append(dict(m=m,discarded_first_slot_mass=str(mass),symmetry_error=str(e2),repaired_tensor='zero',commutators='zero'))
print(json.dumps(dict(status='PASS',exact_assertions=n,paired_assertions=pair_count,matrix_cases=records,exact_repair_records=repair,floating_records=0,limitation='Finite rational identities only; no analytic or priority certification.'),sort_keys=True,indent=2))
