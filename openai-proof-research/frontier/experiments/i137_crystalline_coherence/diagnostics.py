"""Exact finite diagnostics, not an analytic proof or contribution certificate."""
from fractions import Fraction as F
from itertools import product

def run():
 counts={}
 def hit(k,v):
  assert v,k
  counts[k]=counts.get(k,0)+1
 def mul(a,b):return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(2)) for j in range(2)) for i in range(2))
 R=((0,-1),(1,1));I=((1,0),(0,1));G=((F(1),F(1,2)),(F(1,2),F(1)))
 def tr(a):return tuple(zip(*a))
 A=I;vec=[]
 for k in range(6):
  hit('equilateral_metric_rotation',mul(mul(tr(A),G),A)==G)
  vec.append((A[0][0],A[1][0]));A=mul(A,R)
 hit('six_triangle_holonomy',A==I and all(sum(v[i] for v in vec)==0 for i in range(2)))
 for n in (5,7):
  A=I
  for _ in range(n):A=mul(A,R)
  hit('defect_vertex_not_six',A!=I)
 # Average square of an affine scalar function on a triangle:
 # (sum vi^2 + sum i<j vi*vj)/6 >= sum vi^2/12.
 for v in product(range(-4,5),repeat=3):
  sq=sum(x*x for x in v);mix=sum(v[i]*v[j] for i in range(3) for j in range(i+1,3))
  hit('affine_vertex_L2_control',F(sq+mix,6)>=F(sq,12))
 # Exact Fourier selection represented by cyclotomic coefficient reduction:
 # sum_j X^(kj mod m) equals m if k=0 mod m, or has vanishing
 # evaluation at primitive mth roots: use finite character orthogonality in Z_m^2
 # with coefficient counts, avoiding floating complex arithmetic.
 for m in range(2,18):
  for k,l in product(range(m),repeat=2):
   coeff=[0]*m
   for i,j in product(range(m),repeat=2):coeff[(k*i+l*j)%m]+=1
   g=__import__('math').gcd(__import__('math').gcd(k,l),m)
   hit('finite_subgroup_character_selection',all(coeff[n]==(m*g if n%g==0 else 0) for n in range(m)))
 # Ordered moved-row/column identity for arbitrary symmetric pair data.
 for n in range(2,25):
  old=[[F((i+j+1)*(abs(i-j)+1),n+1) for j in range(n)] for i in range(n)]
  new=[r[:] for r in old]
  for j in range(1,n):new[0][j]=new[j][0]=F(j*j+3,n+2)
  diff=sum(new[i][j]-old[i][j] for i in range(n) for j in range(n) if i!=j)
  hit('ordered_one_site_energy_difference',diff==2*sum(new[0][j]-old[0][j] for j in range(1,n)))
 # Original displayed coefficient C0 dominates both original budget polynomials.
 for b,l,h,k,d in product((F(1,2),F(1),F(3,2)),(F(1),F(4),F(100)),(F(1,8),F(1,2)),(F(0),F(1,4),F(1)),(F(0),F(1,3),F(2))):
  C0=101+3*b*l
  actual=51*k+25*(d+h)/(1-h)+b*l*((d+h)/(1-h)+k)
  hit('original_common_constant_coefficients',actual<=C0*(d+h+k))
 # Buffer cardinality L^2 times threshold mass D/tau^2, tau=eta/L.
 for L in range(10,51):
  for den in (3,7,11):
   D=F(1,den);eta=F(1,100);tau=eta/L
   hit('mesoscopic_buffer_scale',L*L*D/(tau*tau)==L**4*D/(eta*eta))
 # Tail substitution alpha=2u has Jacobian 2 and density exponent s/2-1:
 # check rational exponent accounting rather than evaluating special functions.
 for s in (F(0),F(1,4),F(1),F(3,2),F(7,4)):
  hit('heat_tail_scaling_exponent',(s/2-1)+1==s/2)
  if s>0:
   for p in (F(1,4)/s,F(1,2)/s,F(3,4)/s):hit('near_collision_decay_exponent',p*s-1<0)
 return {'status':'PASS','arithmetic':'integers and fractions.Fraction; no numerical analytic certificate','checks':counts,'scope':'finite identities only; not topology of arbitrary meshes, analytic estimates, source truth, external theorem validity, novelty or acceptance'}
if __name__=='__main__':
 import json
 print(json.dumps(run(),indent=2,sort_keys=True))
