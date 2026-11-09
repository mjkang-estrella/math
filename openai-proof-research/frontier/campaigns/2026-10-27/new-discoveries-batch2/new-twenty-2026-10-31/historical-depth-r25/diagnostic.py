# Rational exact diagnostics only; NOT a certified MathDB endpoint.
from fractions import Fraction as F
import json
from pathlib import Path
O=Path(__file__).resolve().parent
def rank(a):
 a=[[F(x) for x in r] for r in a];i=0
 for j in range(len(a[0])):
  k=next((k for k in range(i,len(a)) if a[k][j]),None)
  if k is None:continue
  a[i],a[k]=a[k],a[i];t=a[i][j];a[i]=[x/t for x in a[i]]
  for k in range(len(a)):
   if k!=i:
    t=a[k][j];a[k]=[u-t*v for u,v in zip(a[k],a[i])]
  i+=1
  if i==len(a):break
 return i
# y=z=e1: cross matrices select four distinct bottom-right entries of T1.
ambient=[[int(j==k) for j in range(27)] for k in [4,5,7,8]]
# Camera constraint F_ij=u_i c_j-b_i v_j. Point on valid component u=lambda b,v=lambda c.
b=[2,3];c=[5,7];l=11;u=[l*t for t in b];v=[l*t for t in c];jac=[]
for i in range(2):
 for j in range(2):
  # coordinates (u0,u1,v0,v1,b0,b1,c0,c1)
  jac.append([int(k==i)*c[j] for k in range(2)]+[-int(k==j)*b[i] for k in range(2)]+[-int(k==i)*v[j] for k in range(2)]+[int(k==j)*u[i] for k in range(2)])
assert rank(ambient)==4 and rank(jac)==3
# Polynomial syzygy eliminating fourth equation on b0*c0 !=0.
# b0*c0 F11 = b1*c0 F01 + b0*c1 F10 - b1*c1 F00.
tests=[]
for u,v,b,c in [([13,17],[19,23],[2,3],[5,7]),([0,4],[6,8],[3,0],[9,2])]:
 f=lambda i,j:u[i]*c[j]-b[i]*v[j]
 lhs=b[0]*c[0]*f(1,1);rhs=b[1]*c[0]*f(0,1)+b[0]*c[1]*f(1,0)-b[1]*c[1]*f(0,0);assert lhs==rhs;tests.append([lhs,rhs])
r={'ambient_rank':rank(ambient),'camera_jacobian_rank_at_one_valid_rational_point':rank(jac),'ambient_matrix':ambient,'camera_jacobian':jac,'syzygy_checks':tests,'limits':'Exact arithmetic checks at selected coordinates. Generic codimension and quotient-camera transfer need ordinary proofs; no Lean or discovery certificate.'};(O/'diagnostic.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
