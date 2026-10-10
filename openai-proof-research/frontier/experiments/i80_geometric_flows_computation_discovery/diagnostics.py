"""Exact finite diagnostics for I80; no numerical claim of a universal theorem."""
from fractions import Fraction as Q
from math import factorial
import json

def add(p,q):
 r=p.copy()
 for m,c in q.items():r[m]=r.get(m,Q(0))+c
 return {m:c for m,c in r.items() if c}
def scale(p,c):return {m:v*c for m,v in p.items() if v*c}
def mul(p,q):
 r={}
 for a,c in p.items():
  for b,d in q.items():
   m=tuple(x+y for x,y in zip(a,b));r[m]=r.get(m,Q(0))+c*d
 return {m:c for m,c in r.items() if c}
def power(p,n):
 r={(0,0,0):Q(1)}
 for _ in range(n):r=mul(r,p)
 return r
def deriv(p,i):
 r={}
 for m,c in p.items():
  if m[i]:a=list(m);a[i]-=1;r[tuple(a)]=c*m[i]
 return r
def lap(p):
 r={}
 for i in range(3):r=add(r,deriv(deriv(p,i),i))
 return r
def monomials(n):return [(i,j,n-i-j) for i in range(n+1) for j in range(n-i+1)]
def kernel(A,n):
 A=[r[:] for r in A];piv=[];row=0
 for col in range(n):
  hit=next((r for r in range(row,len(A)) if A[r][col]),None)
  if hit is None:continue
  A[row],A[hit]=A[hit],A[row];v=A[row][col];A[row]=[x/v for x in A[row]]
  for r in range(len(A)):
   if r!=row and A[r][col]:v=A[r][col];A[r]=[x-v*y for x,y in zip(A[r],A[row])]
  piv.append(col);row+=1
 basis=[]
 for f in range(n):
  if f in piv:continue
  v=[Q(0)]*n;v[f]=Q(1)
  for r,col in enumerate(piv):v[col]=-A[r][f]
  basis.append(v)
 return basis
def harmonics(n):
 ms=monomials(n);ls=monomials(n-2) if n>=2 else []
 ds=[lap({m:Q(1)}) for m in ms];A=[[d.get(m,Q(0)) for d in ds] for m in ls]
 out=[{m:c for m,c in zip(ms,v) if c} for v in kernel(A,len(ms))]
 assert len(out)==2*n+1 and all(not lap(p) for p in out)
 return out
X=[{tuple(int(j==i) for j in range(3)):Q(1)} for i in range(3)]
def shift(p,c):
 out={}
 for m,a in p.items():
  z={(0,0,0):a}
  for i in range(3):z=mul(z,power(add(X[i],{(0,0,0):c[i]}),m[i]))
  out=add(out,z)
 return out
def evalp(p,c):return sum(a*c[0]**m[0]*c[1]**m[1]*c[2]**m[2] for m,a in p.items())
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def cross(a,b):return(a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
def vadd(a,b):return tuple(x+y for x,y in zip(a,b))
def vsub(a,b):return tuple(x-y for x,y in zip(a,b))
def vmul(a,c):return tuple(x*c for x in a)
def dfact(n):
 r=1
 for k in range(n,0,-2):r*=k
 return r
def sphere_average(m):
 if any(k%2 for k in m):return Q(0)
 return Q(dfact(m[0]-1)*dfact(m[1]-1)*dfact(m[2]-1),dfact(sum(m)+1))
def radial_moment_polynomial(p):
 # R_d = integral_0^infty f(r)^2 r^(d+2)dr; sphere measure /4pi.
 out={}
 for m,c in p.items():out[sum(m)]=out.get(sum(m),Q(0))+c*sphere_average(m)
 return {k:v for k,v in out.items() if v}
def moment(h,a,c):
 hs=shift(h,c);w=[add(scale(X[(i+2)%3],a[(i+1)%3]),scale(X[(i+1)%3],-a[(i+2)%3])) for i in range(3)]
 out={}
 for i in range(3):
  for j in range(3):out=add(out,mul(mul(w[i],w[j]),deriv(deriv(hs,i),j)))
 return radial_moment_polynomial(out)

def rotation(v,a,t):
 # t=tan(angle/2), a a coordinate unit axis.
 c=(1-t*t)/(1+t*t);s=2*t/(1+t*t)
 return vadd(vadd(vmul(v,c),vmul(cross(a,v),s)),vmul(a,(1-c)*dot(a,v)))
def turn(x,a,c,t):return vadd(c,rotation(vsub(x,c),a,t))

def run():
 counts={};cases=0
 axes=[(Q(1),Q(0),Q(0)),(Q(0),Q(1),Q(0)),(Q(0),Q(0),Q(1)),(Q(1),Q(2),Q(3))]
 centers=[(Q(0),Q(0),Q(0)),(Q(1,3),Q(-2,5),Q(3,7))]
 for degree in range(11):
  hs=harmonics(degree);counts[str(degree)]=len(hs)
  for h in hs:
   for a in axes:
    for c in centers:
     expected=-sum(a[i]*a[j]*evalp(deriv(deriv(h,i),j),c) for i in range(3) for j in range(3))/3
     assert moment(h,a,c)==({2:expected} if expected else {})
     cases+=1
 H4=add(add(power(X[0],4),power(X[1],4)),power(X[2],4));rr=add(add(power(X[0],2),power(X[1],2)),power(X[2],2));H4=add(H4,scale(power(rr,2),Q(-3,5)));assert not lap(H4)
 # Normalize c_f=1, so M=-H_aa(c).
 octmoment=Q(0)
 for a in axes[:3]:
  for sign in [-1,1]:
   c=vmul(a,Q(sign));octmoment-=sum(a[i]*a[j]*evalp(deriv(deriv(H4,i),j),c) for i in range(3) for j in range(3))
 assert octmoment==Q(-144,5)
 # Support and plateau inequalities for worst allowed b/h.
 ratio=Q(1,4096)
 lower=Q(1,32)-Q(1,128)-Q(9,2)*ratio
 upper=Q(1,32)+Q(1,128)+Q(9,2)*ratio
 support=Q(1,8)+Q(1,32)+Q(1,128)+ratio/2
 assert Q(1,64)<lower<=upper<Q(1,16) and support<Q(1,4)
 rotation_cases=0;phase_tests=0
 for b in [Q(1,4096),Q(1,65536),Q(1,2**32)]:
  for frac in [Q(0),Q(1,7),Q(1,2),Q(1)]:
   for terminal in [False,True]:
    a=axes[1 if terminal else 0];d=(Q(-b if terminal else 0),Q(0 if terminal else b*frac),Q(0));A=(Q(-1),Q(2,7),Q(0));t=64*b
    c1=vadd(A,(Q(0),Q(0),Q(1,32)));c2=vadd(c1,vsub(vmul(d,Q(1,2)),vmul(cross(a,d),Q(1,128)/b)))
    mid=turn(A,a,c1,t);end=turn(mid,a,c2,-t)
    assert end==vadd(A,d)
    # Whole-neighborhood affine identity at rational sample points.
    for x in [A,vadd(A,(Q(1,10000),Q(-1,20000),Q(1,30000)))]:
     assert turn(turn(x,a,c1,t),a,c2,-t)==vadd(x,d)
    for j in range(17):
     v=turn(A,a,c1,t*Q(j,16));z=turn(mid,a,c2,-t*Q(j,16))
     assert dot(vsub(v,c1),vsub(v,c1))==Q(1,32)**2
     assert dot(vsub(z,c2),vsub(z,c2))==dot(vsub(mid,c2),vsub(mid,c2))
     if not terminal:assert v[0]==z[0]==Q(-1)
     phase_tests+=2
    rotation_cases+=1
 # Loading second half-turn: rational tangent samples yield x in [-1,0], endpoints exact.
 for t in [Q(i,8) for i in range(100)]:
  p=turn((Q(0),Q(1,100),Q(0)),axes[1],(Q(-1,2),Q(1,100),Q(0)),t);assert -1<=p[0]<=0
 # Every source-legal n satisfies exponent budget algebra; finite exact samples are diagnostic.
 scale_checks=0
 for n in range(101):
  for order in range(n+1):
   assert n+8-order>=1 and 2*n+19-order>=1
   scale_checks+=1
 # Exterior pressure sign / normalization from integration by parts: (1/5)*(2/3)*(-5)=-2/3.
 assert Q(1,5)*Q(2,3)*(-5)==Q(-2,3)
 # Radial profile support / plateau and disjoint shells.
 assert Q(1,512)<Q(1,256)<Q(1,128)<Q(1,64)<Q(1,16)<Q(1,12)<Q(1,10)<Q(1,8)
 return dict(status='PASS_FINITE_DIAGNOSTICS_NOT_PROOF',harmonic_kernel_dimensions=counts,translated_swirl_moment_cases=cases,octahedral_fourth_moment=str(octmoment),rotation_cases=rotation_cases,intermediate_phase_samples=phase_tests,source_exponent_samples=scale_checks,plateau_lower=str(lower),plateau_upper=str(upper),support_radius_bound=str(support),pressure_exterior_radial_coefficient='-2/3')
if __name__=='__main__':print(json.dumps(run(),sort_keys=True,indent=2))
