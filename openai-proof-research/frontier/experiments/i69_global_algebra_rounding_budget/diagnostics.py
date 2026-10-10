"""Independent finite I69 checks. Exact fractions unless explicitly labeled floating.
No prior diagnostic imports, no writes, no network, no universal-proof claim.
"""
from fractions import Fraction as F
from itertools import product,combinations_with_replacement,permutations
import random,json,math
N=0
def ck(x):
 global N;N+=1
 assert x

def mat(n):return [[F(0) for _ in range(n)] for _ in range(n)]
def mm(a,b):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def add(a,b,s=1):return [[x+s*y for x,y in zip(r,t)] for r,t in zip(a,b)]
def tr(a):return sum(a[i][i] for i in range(len(a)))
def norm(a):return sum(x*x for row in a for x in row)
def inner(a,b):return sum(x*y for r,t in zip(a,b) for x,y in zip(r,t))
def comm(a,b):return add(mm(a,b),mm(b,a),-1)
def tensor(n):return [[[F(0) for k in range(n)] for j in range(n)] for i in range(n)]
def slices(T):return [[[T[i][j][k] for j in range(len(T))] for i in range(len(T))] for k in range(len(T))]
def data(T):
 n=len(T);A=slices(T);B=mat(n)
 for a in A:B=add(B,mm(a,a))
 E=sum(norm(comm(a,b)) for a in A for b in A)
 beta=sum((B[i][j]-(i==j))**2 for i in range(n) for j in range(n))
 return A,B,E,beta
rng=random.Random(690091)
block_cases=0
for n in range(2,6):
 for case in range(8):
  T=tensor(n)
  for ijk in combinations_with_replacement(range(n),3):
   v=F(rng.randrange(-3,4),7)
   if ijk[0]==ijk[1]==0 and ijk[2]>0:v=F(0)
   for p in set(permutations(ijk)):T[p[0]][p[1]][p[2]]=v
  A,B,E,beta=data(T);S=[[r[1:] for r in q[1:]] for q in T[1:]]
  C,Bp,Ep,betap=data(S);H=[r[1:] for r in A[0][1:]];H2=mm(H,H);H3=mm(H2,H);H4=mm(H2,H2)
  c=T[0][0][0];h=norm(H);a=norm(add(H2,H,-c));L=sum(norm(comm(H,z)) for z in C)
  w=[inner(H,z) for z in C];w2=sum(x*x for x in w);nu=1-c*c-h
  ck(B[0][0]==c*c+h)
  for i,j in product(range(n-1),repeat=2):ck(B[i+1][j+1]==Bp[i][j]+2*H2[i][j])
  for i in range(n-1):ck(B[0][i+1]==w[i])
  ck(E+beta-Ep-betap==nu*nu-4*nu*h-2*h*h-8*c*tr(H3)+6*tr(H4)+6*L+6*w2)
  Wnorm=F(0);CW=F(0)
  for i,j in product(range(n-1),repeat=2):
   W=[[H[x][i]*H[y][j]-H[x][j]*H[y][i] for y in range(n-1)] for x in range(n-1)]
   Wnorm+=norm(W);CW+=inner(comm(C[i],C[j]),W)
  ck(Wnorm==2*(h*h-tr(H4)))
  ck(E==Ep+4*a+4*L+2*CW+Wnorm)
  block_cases+=1
# Global scalar unitalization: direct product computation, arbitrary linked tensors.
for n in range(2,5):
 for case in range(3):
  T=tensor(n)
  for ijk in combinations_with_replacement(range(n),3):
   v=F(rng.randrange(-2,3),5)
   for p in set(permutations(ijk)):T[p[0]][p[1]][p[2]]=v
  A,B,E,beta=data(T);alpha=F(2,7);U=tensor(n+1)
  for i,j,k in product(range(n),repeat=3):U[i+1][j+1][k+1]=T[i][j][k]
  U[0][0][0]=alpha
  for i in range(1,n+1):
   for p in set(permutations((0,i,i))):U[p[0]][p[1]][p[2]]=alpha
  AU,BU,EU,bU=data(U);tau=[tr(a) for a in A]
  ck(AU[0]==[[alpha*(i==j) for j in range(n+1)] for i in range(n+1)])
  ck(EU==E+4*alpha**2*(sum(x*x for x in tau)-tr(B))+2*n*(n-1)*alpha**4)
  ck(BU[0][0]==(n+1)*alpha**2)
  for i in range(n):ck(BU[0][i+1]==alpha*tau[i])
  for i,j in product(range(n),repeat=2):ck(BU[i+1][j+1]==B[i][j]+2*alpha**2*(i==j))

# Complete stationary-coordinate chains with B <= I by a conservative entry scale.
chain_cases=0
for n in range(1,8):
 for case in range(4):
  T=tensor(n)
  for ijk in combinations_with_replacement(range(n),3):
   i,j,k=ijk;v=F(rng.randrange(-2,3),10*n*n)
   if i==j<k:v=F(0)
   if i==j==k:v=abs(v)
   for p in set(permutations(ijk)):T[p[0]][p[1]][p[2]]=v
  A,B,E,beta=data(T);b=tr(B);M=sum(T[i][j][k]**2 for i,j,k in product(range(n),repeat=3) if not i==j==k)
  # row-sum norm upper bound certifies B <= I for these tiny examples
  ck(max(sum(abs(v) for v in row) for row in B)<=1)
  c=[T[i][i][i] for i in range(n)];cost=M+sum((1-x)**2 for x in c)
  ck(sum(1-x*x for x in c)==n-b+M)
  ck(cost<=n-b+2*M)
  ck(sum(1 for x in c if x<F(1,2))*F(3,4)<=n-b+M)
  chain_cases+=1
# Exact potential obstruction: T=(2 x^3+3 x y^2)/sqrt(5).
# Work with unscaled integral tensor and scale quadratic/quartic expressions.
T=tensor(2);T[0][0][0]=2
for p in set(permutations((0,1,1))):T[p[0]][p[1]][p[2]]=1
A,B,E,_=data(T);ck(B==[[F(5),F(0)],[F(0),F(2)]])
ck(E/F(25)==F(4,25));ck(sum((B[i][j]/5-(i==j))**2 for i,j in product(range(2),repeat=2))==F(9,25))
ck(F(13,25)<1)
# Walsh linked tensors: no square roots are used in the exact representation.
walsh=[]
for k in [2,3,4]:
 m=2**k-1;T=tensor(m)
 for i,j in product(range(1,m+1),repeat=2):
  t=i^j
  if t:T[i-1][j-1][t-1]=F(1)
 A,B,E,_=data(T)
 for i,j in product(range(m),repeat=2):ck(B[i][j]==(m-1)*(i==j))
 for i,j in product(range(m),repeat=2):
  C=comm(A[i],A[j])
  for a,b in product(range(m),repeat=2):ck(C[a][b]==-int(a==i and b==j)+int(a==j and b==i))
 ck(E/F((m-1)**2)==F(2*m,m-1))
 for i,j in product(range(m),repeat=2):ck(T[i][i][j]==0)
 # Rational orthogonal pair moves: diagonal cubic remains identically zero.
 for i,j in [(0,1),(0,m-1),(m//2,m-1)]:
  for c,s in [(F(3,5),F(4,5)),(F(5,13),F(-12,13))]:
   u=[F(0)]*m;v=u.copy();u[i]=c;u[j]=s;v[i]=-s;v[j]=c
   ck(sum(T[a][b][d]*u[a]*u[b]*u[d] for a,b,d in product([i,j],repeat=3))==0)
   ck(sum(T[a][b][d]*v[a]*v[b]*v[d] for a,b,d in product([i,j],repeat=3))==0)
 # Subset support bound for deterministic partitions of various block sizes.
 for b in range(1,m+1):
  for start in range(0,m,b):
   J=list(range(start,min(m,start+b)));q=len(J)
   ck(sum(T[x][y][z]**2 for x,y,z in product(J,repeat=3))<=q*(q-1))
 # Integer Walsh matrix verifies the actual coordinate-dilation linkage.
 chars=[[1 if (g&i).bit_count()%2==0 else -1 for i in range(1,m+1)] for g in range(m+1)]
 for i,j in product(range(m),repeat=2):ck(sum(row[i]*row[j] for row in chars)==(m+1)*(i==j))
 for i,j,t in product(range(m),repeat=3):ck(sum(row[i]*row[j]*row[t] for row in chars)==(m+1)*T[i][j][t])
 # Full Hessian on two simultaneous rotations detects every x xor y=z triple.
 ck(T[0][1][2]==1)
 H=mat(m);H[0][1]=H[0][2]=1;H[1][0]=H[2][0]=-1
 H2=mm(H,H)
 second=6*sum(T[i][j][t]*H[j][i]*H[t][i] for i,j,t in product(range(m),repeat=3))+3*sum(T[i][i][j]*H2[j][i] for i,j in product(range(m),repeat=2))
 ck(second==12)
 walsh.append(dict(m=m,E=str(F(2*m,m-1)),hessian_unscaled=str(second)))
# Independent audit of I65 scalar rounding identity and exact simplex chain budgets.
for z in [F(a,8) for a in range(25)]:
 for h in [F(a,9) for a in range(20)]:ck((z-1)**2 <= (z*z+h-1)**2+2*h)
for m in [2,3,5,8,17,63,127,512]:
 r=F(m+1,m-1);M=F(0);sumc2=F(0);charge=F(0)
 for d in range(m,1,-1):
  t2=r*F(d-1,d+1);h2=t2/d;c2=t2*F(d-1,d);M+=3*h2;sumc2+=c2
  ck(F(1,3)<=t2<=1);ck(c2>=F(1,6));ck(t2-2*t2/F(d*(d-1))==(r*F(d-2,d) if d>2 else 0))
  charge+=t2*t2/F(d-1)
 ck(sumc2+M==m);ck(charge==r*r*sum((F(1,j)-F(2,j*j) for j in range(3,m+2)),F(0)))
# Floating formula evaluations: not intervals or proof certificates.
floats=[]
def block(d,t):
 r=(d+1)/(d-1);cs=[math.sqrt(r)*(j-1)/math.sqrt(j*(j+1)) for j in range(2,d+1)]+[0]
 M=3*r*sum((j-1)/(j*(j+1)) for j in range(2,d+1))
 g=t*t*M+sum((1-t*c)**2 for c in cs)
 R=d*(1-t*t)**2+2*d*t**4/(d-1)
 return g,R
for blocks in [[(2,1),(7,1),(31,1)],[(4096,1)],[(2**j,1-1/(2**j)) for j in range(1,12)],[(3,.2),(128,.8),(2048,1)],[(2,1)]*100]:
 m=sum(d for d,t in blocks);v=[block(d,t) for d,t in blocks];g=sum(x[0] for x in v);r=sum(x[1] for x in v)
 floats.append(dict(kind='uncertified block formula',m=m,residual=r,greedy_cost=g,log_budget=r*math.log(math.e+m/r),ratio=g/(r*math.log(math.e+m/r))))
for count,d in [(1,16),(10,128),(100,2048),(1000,32768)]:
 eta=count/(d-1);eps=-2*math.expm1(count*math.log1p(-1/(d-1)))
 codim_ratio=math.expm1(count*math.log1p(1/d));scale2=math.exp(count*math.log1p(2/(d-1)))
 bound=32*scale2*codim_ratio+2*(math.sqrt(scale2)-1)**2
 floats.append(dict(kind='uncertified tensor-product dilation',factors=count,block_dimension=d,log_dimension=count*math.log(d),eta=eta,epsilon=eps,normalized_bound=bound))
floats.append(dict(kind='uncertified failed-potential values',before=13/25*math.log(math.e+50/13),after=math.log(math.e+1)))
print(json.dumps(dict(scope='Finite independent checks; no universal proof certification',exact_assertions=N,block_identity_cases=block_cases,chain_cases=chain_cases,walsh_cases=walsh,floating_records=floats),indent=2,sort_keys=True))
