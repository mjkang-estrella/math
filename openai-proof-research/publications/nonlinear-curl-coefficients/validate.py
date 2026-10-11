"""Finite algebraic transcription checks. These are not a proof certificate."""
from fractions import Fraction as F
import itertools, random, json
rng=random.Random(14013)
checks=0
def check(a,b):
 global checks
 assert a==b,(a,b)
 checks+=1
def matmul(A,B):
 n=len(A);return [[sum(A[i][k]*B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
def add(A,B):return [[a+b for a,b in zip(x,y)] for x,y in zip(A,B)]
def sub(A,B):return [[a-b for a,b in zip(x,y)] for x,y in zip(A,B)]
def norm2(A):return sum(a*a for row in A for a in row)
def mv(A,v):return [sum(a*b for a,b in zip(row,v)) for row in A]
for n in range(1,6):
 for trial in range(12):
  X=[]
  for r in range(n):
   A=[[F(rng.randrange(-3,4),3) for _ in range(n)] for _ in range(n)]
   X.append([[A[min(i,j)][max(i,j)] for j in range(n)] for i in range(n)])
  B=[[sum(matmul(A,A)[i][j] for A in X) for j in range(n)] for i in range(n)]
  S=lambda i,r,s:X[r][i][s]-X[s][i][r]
  symerr=F(0);snorm=F(0)
  for i,j,r in itertools.product(range(n),repeat=3):
   val=sum(X[c][a][b] for a,b,c in itertools.permutations((i,j,r)))/6
   symerr+=(X[r][i][j]-val)**2;snorm+=S(i,r,j)**2
  check(3*symerr,snorm)
  for r,s,t in itertools.product(range(n),repeat=3):
   C=sub(matmul(X[r],X[s]),matmul(X[s],X[r]))
   Z=sub(add(matmul(X[r],X[t]),matmul(X[t],X[r])),[[0]*n for _ in range(n)])
   T=add(matmul(X[s],X[t]),matmul(X[t],X[s]))
   errors=[mv(X[r],[S(i,t,s) for i in range(n)]),mv(X[s],[S(i,t,r) for i in range(n)]),mv(X[t],[S(i,r,s) for i in range(n)])]
   for i in range(n):check(Z[i][s]-T[i][r],C[i][t]+errors[0][i]-errors[1][i]+errors[2][i])
  # Wick expansion against exact products, including crossing terms.
  wick=[[F(0) for _ in range(n)] for _ in range(n)]
  for r,s in itertools.product(range(n),repeat=2):
   for seq in [(r,r,s,s),(r,s,s,r),(r,s,r,s)]:
    P=X[seq[0]]
    for k in seq[1:]:P=matmul(P,X[k])
    wick=add(wick,P)
  rhs=matmul(B,B)
  for A in X:rhs=add(rhs,matmul(matmul(A,B),A))
  for A in X:
   for C in X:rhs=add(rhs,matmul(matmul(matmul(A,C),A),C))
  check(wick,rhs)
# Scalar reflected elimination with a globally increasing, strictly convex f
# on [-2,2]: f(a)=a+a^2/8; a_R=1/2,h_R=1/4 there.
def dd(a,b):return 1+(a+b)/8
for a,b,c,A,C in itertools.product(map(F,[-2,-1,0,1,2]),repeat=5):
 ep=dd(a,b)*A-dd(a,c)*C;em=dd(-a,-b)*A-dd(-a,-c)*C
 assert (A-C)**2<=8*(ep*ep+em*em)
 M=16*4*4+16*16*(1+8)
 assert ((a+b)*A-(a+c)*C)**2<=M*(ep*ep+em*em)
 checks+=2
print(json.dumps({'status':'PASS','exact_assertions':checks,'dimensions':[1,2,3,4,5],'scope':'finite coefficient identities, Wick contractions, repeated spectral values; not universal proof verification'},indent=2))
