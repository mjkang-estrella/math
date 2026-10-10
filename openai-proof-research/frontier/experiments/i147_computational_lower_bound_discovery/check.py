"""New finite exact checks only. No inherited diagnostics or analytic certification."""
from fractions import Fraction as F
from itertools import product
from collections import Counter

def run():
 counts=Counter()
 y=[(2,1,0),(1,2,0),(0,2,1),(0,1,2),(1,0,2),(2,0,1)]
 edges=[(i,(i+1)%6) for i in range(6)]+[((i+1)%6,i) for i in range(6)]
 for rare in [(0,1),(0,2),(1,2)]:
  ledger={(i,j):sum(y[j][r]-y[i][r] for r in rare) for i,j in edges}
  assert sorted(ledger.values())==[-1]*4+[0]*4+[1]*4
  counts['ring_derivative_rows']+=len(ledger)
 exact={(i,j):sum(y[j][r]-y[i][r] for r in (1,2)) for i,j in edges}
 assert {e for e,b in exact.items() if b==1}=={(0,1),(5,4),(1,2),(4,3)}
 assert {e for e,b in exact.items() if b==-1}=={(1,0),(4,5),(2,1),(3,4)}
 for r in range(3):
  assert sum(max(0,y[i][r]-y[j][r]) for i,j in edges)==4
  counts['coordinate_consumption_counts']+=1
 # A*(B²+C²)+BC*(B+C) = (1-B-C)*(B²+C²)+BC*(B+C).
 # w² minus this polynomial = 2BC+B³+C³, nonnegative on simplex.
 def polyadd(a,b):
  z=Counter(a);z.update(b);return {k:v for k,v in z.items() if v}
 harm={(0,2):1,(2,0):1,(3,0):-1,(0,3):-1}
 w2={(2,0):1,(1,1):2,(0,2):1}
 assert polyadd(w2,{k:-v for k,v in harm.items()})=={(1,1):2,(3,0):1,(0,3):1}
 counts['exact_harmful_polynomial_identity']=1
 bits=list(product((0,1),repeat=3));dim=len(bits)
 pairs=[(F(3,5),F(4,5)),(F(5,13),F(12,13)),(F(8,17),F(15,17))]
 def prod(xs):
  z=F(1)
  for x in xs:z*=x
  return z
 def dot(a,b):return sum(x*y for x,y in zip(a,b))
 # Real unitary: rational local rotations followed by Toffoli, then local rotations.
 def local_matrix(ps):return [[prod(((ps[i][0] if a[i]==b[i] else (-ps[i][1] if a[i]==0 else ps[i][1])) for i in range(3))) for b in bits] for a in bits]
 def mm(a,b):return [[sum(a[i][k]*b[k][j] for k in range(dim)) for j in range(dim)] for i in range(dim)]
 def tr(a):return list(map(list,zip(*a)))
 local=local_matrix(pairs);perm=[[F(0) for _ in bits] for _ in bits]
 for j,b in enumerate(bits):
  a=(b[0],b[1],b[2]^(b[0]&b[1]));perm[bits.index(a)][j]=F(1)
 c=mm(local,mm(perm,local));assert mm(tr(c),c)==[[F(i==j) for j in range(dim)] for i in range(dim)]
 q=[[sum(c[k][i]*c[k][j] for k,b in enumerate(bits) if b[2]==0) for j in range(dim)] for i in range(dim)]
 f=[2*q[j][j]-1 for j in range(dim)];p=[v*v for _,v in pairs]
 mu=[prod(p[i] if b[i] else 1-p[i] for i in range(3)) for b in bits]
 coeff=[]
 for mask in bits:
  ch=[prod((p[i]-b[i])/(pairs[i][0]*pairs[i][1]) for i in range(3) if mask[i]) for b in bits]
  fh=sum(mu[j]*f[j]*ch[j] for j in range(dim));coeff.append(fh)
  if any(mask):
   values=[]
   for h in bits:
    v=[prod((pairs[i][b[i]])*((-1)**(h[i]*b[i])) for i in range(3)) for b in bits]
    w=[prod(((pairs[i][1] if b[i]==0 else -pairs[i][0]) if mask[i] else pairs[i][b[i]])*((-1)**(h[i]*b[i])) for i in range(3)) for b in bits]
    values.append(sum(w[i]*q[i][j]*v[j] for i in range(dim) for j in range(dim)))
   assert fh==2*sum(values)/dim
   assert fh*fh<=4*sum(z*z for z in values)/dim
   counts['biased_phase_average_coefficients']+=1
 energy=F(0)
 for i in range(3):
  for j,b in enumerate(bits):
   if b[i]:continue
   other=list(b);other[i]=1;j1=bits.index(tuple(other))
   energy+=(mu[j]+mu[j1])*p[i]*(1-p[i])*(f[j]-f[j1])**2
 assert energy==sum(sum(mask)*x*x for mask,x in zip(bits,coeff))
 counts['biased_dirichlet_identity']=1
 # Physical conditional variances on an exact rational 4-cycle Ising law.
 b4=list(product((-1,1),repeat=4));ts=[F(1,3),F(-1,4),F(2,5),F(1,5)]
 weights={b:prod(1+ts[i]*b[i]*b[(i+1)%4] for i in range(4))*prod(1+F(i+1,10)*b[i] for i in range(4)) for b in b4}
 norm=sum(weights.values());mass={b:v/norm for b,v in weights.items()}
 vals={b:F((7*b[0]+3*b[1]*b[2]-2*b[3]),12) for b in b4}
 for cls in [(0,2),(1,3)]:
  out=[i for i in range(4) if i not in cls]
  physical=F(0);conditional=F(0)
  for eta in product((-1,1),repeat=2):
   group=[b for b in b4 if tuple(b[i] for i in out)==eta];m=sum(mass[b] for b in group);prob={b:mass[b]/m for b in group}
   plus={i:sum(prob[b] for b in group if b[i]==1) for i in cls}
   for b in group:assert prob[b]==prod(plus[i] if b[i]==1 else 1-plus[i] for i in cls)
   for i in cls:
    for b in group:
     if b[i]!=-1:continue
     bp=list(b);bp[i]=1;bp=tuple(bp);delta=(vals[b]-vals[bp])**2
     physical+=mass[b]*mass[bp]/(mass[b]+mass[bp])*delta
     conditional+=m*(prob[b]+prob[bp])*plus[i]*(1-plus[i])*delta
   counts['color_conditioned_product_laws']+=1
  assert physical==conditional
  counts['color_dirichlet_decompositions']+=1
 for m in range(1,6):
  n=2*m;t=F(1,3);rhos=[prod(1+t*b[2*i]*b[2*i+1] for i in range(m)) for b in product((-1,1),repeat=n)]
  assert sum(x*x for x in rhos)/2**n==(1+t*t)**m
  assert max(rhos)==(1+t)**m
  counts['matching_density_exact_instances']+=1
 return {'status':'PASS','counts':dict(sorted(counts.items())),'scope':'Finite exact rational identities only; no universal mathematics, Gaussian integration, asymptotics or contribution certification'}
if __name__=='__main__':
 import json
 print(json.dumps(run(),indent=2))
