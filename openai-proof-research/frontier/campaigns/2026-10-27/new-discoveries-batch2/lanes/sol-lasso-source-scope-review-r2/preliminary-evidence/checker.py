from fractions import Fraction as Q
from pathlib import Path
import json,itertools,datetime
P=Path(__file__).resolve().parent
c=Q(-49999,100000); l=Q(1,20)
C=[[Q(1) if i==j else c for j in range(3)] for i in range(3)]
def inv(a):
 n=len(a); b=[row[:]+[Q(i==j) for j in range(n)] for i,row in enumerate(a)]
 for j in range(n):
  p=next(i for i in range(j,n) if b[i][j]); b[j],b[p]=b[p],b[j]
  z=b[j][j]; b[j]=[x/z for x in b[j]]
  for i in range(n):
   if i!=j:
    z=b[i][j]; b[i]=[x-z*y for x,y in zip(b[i],b[j])]
 return [r[n:] for r in b]
D=[[Q(0)]*3 for _ in range(3)]; L=[[Q(i==j) for j in range(3)] for i in range(3)]
for i in range(3):
 D[i][i]=C[i][i]-sum(L[i][a]**2*D[a][a] for a in range(i)); assert D[i][i]>0
 for j in range(i+1,3): L[j][i]=(C[j][i]-sum(L[j][a]*L[i][a]*D[a][a] for a in range(i)))/D[i][i]
records=[]
for A in itertools.combinations(range(3),2):
 I=next(i for i in range(3) if i not in A); B=inv([[C[i][j] for j in A] for i in A]); R=[sum(C[I][A[j]]*B[j][i] for j in range(2)) for i in range(2)]
 v=C[I][I]-sum(R[j]*C[A[j]][I] for j in range(2)); assert v==Q(149999,2500050000)
 for z in itertools.product([-1,1],repeat=2):
  m=l*sum(R[i]*z[i] for i in range(2))
  cov=[[z[i]*B[i][j]*z[j] for j in range(2)] for i in range(2)]
  if sum(z)==0:
   assert m==0 and cov[0][1]/cov[0][0]==c
   assert all(sum(B[i][j]*z[j] for j in range(2))==z[i]/(1-c) for i in range(2))
  records.append({'support':A,'sign':z,'inactive_mean':str(m),'schur':str(v)})
assert 1-v/l**2>Q(122,125)
assert 1-c*c>Q(17,20)**2 and 0<(1+c)/(1-c)<1
assert Q(3,8)*(Q(4,5)-Q(4,5)**3/6)>Q(1,4)
# Alternative uniform cubic proof: derivative y*(18/5-6*y), positive to3/5 then negative.
# Evaluate derivative and endpoint/stationary values exactly; no reused factor vectors.
A=Q(9,5); y=Q(3,5)
assert 2*A*y-6*y*y==0 and A*y*y-2*y**3==Q(27,125)
# Polynomial identity checked at four distinct points determines a cubic.
for y in [Q(0),Q(1,7),Q(2,3),Q(11,5)]:
 assert A**3/27-y*y*(A-2*y)==(A-3*y)**2*(A+6*y)/27
assert Q(61,250)-Q(27,125)==Q(7,250)
# Centering isometry Q has rational Hadamard columns /2.
H=[[Q(s,2) for s in r] for r in [[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]]]
assert all(sum(H[r][j] for r in range(4))==0 for j in range(3))
assert all(sum(H[r][i]*H[r][j] for r in range(4))==int(i==j) for i in range(3) for j in range(3))
(P/'checker-results.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','method':'Gauss-Jordan inverse, full3x3 LDL, all supports/all signs, derivative cubic maximum plus four-point polynomial test, rational Hadamard isometry','pivots':[str(D[i][i]) for i in range(3)],'events':records,'scope':'Exact finite arithmetic and rational analytic premises only; Gaussian/KKT/exp/pi facts reviewed in prose; not formal certification'},indent=2))
print('PASS independent exact checker')
