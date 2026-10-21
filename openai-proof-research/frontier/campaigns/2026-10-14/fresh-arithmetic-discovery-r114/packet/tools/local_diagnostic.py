"""Bounded exact sanity checks only; no global theorem or formal certificate."""
import itertools,json

def mul(x,y,p=None):
 a,b,z=x; c,d,w=y
 ans=(a+c,b+d,z+w+a*d-b*c)
 return tuple(t%p for t in ans) if p else ans

def inv(x,p=None):
 ans=tuple(-t for t in x)
 return tuple(t%p for t in ans) if p else ans

def mm(A,B): return [[sum(a*b for a,b in zip(row,col)) for col in zip(*B)] for row in A]
def tr(A): return list(map(list,zip(*A)))
def nmat(a,b,z): return [[1,a,b,z],[0,1,0,b],[0,0,1,-a],[0,0,0,1]]
J=[[0,0,0,1],[0,0,1,0],[0,-1,0,0],[-1,0,0,0]]
rows=[]
for p in (2,3,5):
 xs=list(itertools.product(range(p),repeat=3)); noncomm=0
 for x in xs:
  N=nmat(*x); assert [[v%p for v in row] for row in mm(mm(tr(N),J),N)]==[[v%p for v in row] for row in J]
  for y in xs:
   z=mul(x,y,p); P=mm(nmat(*x),nmat(*y))
   assert [[v%p for v in row] for row in P]==[[v%p for v in row] for row in nmat(*z)]
   comm=mul(mul(mul(x,y,p),inv(x,p),p),inv(y,p),p)
   assert comm==(0,0,2*(x[0]*y[1]-x[1]*y[0])%p)
   noncomm+=comm!=(0,0,0)
 rows.append(dict(p=p,elements=len(xs),ordered_pairs=len(xs)**2,noncommuting_pairs=noncomm))
# General k=2,m=1 examples, with free symmetric central coordinates.
for vals in itertools.product((-1,0,2),repeat=4):
 A=[list(vals[:2]),list(vals[2:])]; Jw=[[0,1],[-1,0]]
 S=mm(mm(A,Jw),tr(A)); Q=[[0,S[0][1]],[0,0]]
 Z=[[2,-3],[-3,5]]; B=[[Q[i][j]+Z[i][j] for j in range(2)] for i in range(2)]; C=mm(Jw,tr(A))
 N=[[int(i==j) for j in range(6)] for i in range(6)]
 O=[[0]*6 for _ in range(6)]
 for i in range(2):
  O[i][4+i]=1; O[4+i][i]=-1
  for j in range(2):
   O[2+i][2+j]=Jw[i][j]; N[i][2+j]=A[i][j];N[i][4+j]=B[i][j];N[2+i][4+j]=C[i][j]
 assert mm(mm(tr(N),O),N)==O
print(json.dumps(dict(purpose='finite local sanity checks, not global density proof',line_parabolic=rows,higher_block_integer_cases=81),indent=2))
