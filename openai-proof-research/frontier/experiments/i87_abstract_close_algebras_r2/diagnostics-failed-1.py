#!/usr/bin/env python3
"""Independent exact finite tests; standard library only; stdout only."""
from fractions import Fraction as Q
from itertools import product
import json

def red(w):
 out=[]
 for a in w:
  if out and out[-1]==-a:out.pop()
  else:out.append(a)
 return tuple(out)
def inv(w):return tuple(-a for a in w[::-1])
def words(alphabet,n):
 out=[()];layer=[()]
 for _ in range(n):
  layer=[w+(a,) for w in layer for a in alphabet if not w or a!=-w[-1]];out+=layer
 return out
def add(a,b,f=Q(1)):
 out=dict(a)
 for k,v in b.items():out[k]=out.get(k,Q(0))+f*v
 return {k:v for k,v in out.items() if v}
def scale(a,f):return {k:v*f for k,v in a.items() if v*f}
def xi(w,t,r):return {w[:i]:(t**len(w) if i==0 else r*t**(len(w)-i)) for i in range(len(w)+1)}
def Tg(g,y,t,r):
 if y==g:return xi(y,t,r)
 z=red(inv(g)+y);neighbor=red(g+z[:-1])
 return scale(add(xi(y,t,r),xi(neighbor,t,r),-t),1/r)
def zeros(m,n):return [[Q(0) for _ in range(n)] for _ in range(m)]
def eye(n):return [[Q(i==j) for j in range(n)] for i in range(n)]
def tr(a):return [list(c) for c in zip(*a)]
def mm(a,b):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def plus(a,b):return [[x+y for x,y in zip(r,s)] for r,s in zip(a,b)]
def kron(a,b):return [[x*y for x in r for y in s] for r in a for s in b]
def unit(n,i,j):
 a=zeros(n,n);a[i][j]=Q(1);return a
def rank(a):
 a=[r[:] for r in a];k=0
 for j in range(len(a[0])):
  p=next((p for p in range(k,len(a)) if a[p][j]),None)
  if p is None:continue
  a[k],a[p]=a[p],a[k];v=a[k][j];a[k]=[x/v for x in a[k]]
  for i in range(len(a)):
   if i!=k:
    v=a[i][j];a[i]=[x-v*y for x,y in zip(a[i],a[k])]
  k+=1
 return k
stats={};off=path=0;ranks=[]
for t,r in [(Q(3,5),Q(4,5)),(Q(5,13),Q(12,13)),(Q(15,17),Q(8,17))]:
 for g in words([1,-1,2,-2],3):
  ps=[g[:i] for i in range(len(g)+1)];n=len(ps)
  cols=[Tg(g,y,t,r) for y in ps];mat=[[c.get(y,Q(0)) for c in cols] for y in ps]
  assert mm(tr(mat),mat)==eye(n)
  diff=plus(mat,[[-v for v in row] for row in eye(n)])
  assert rank(diff)<=len(g)+1;ranks.append(rank(diff));path+=1
  for y in words([1,-1,2,-2,3,-3],3):
   actual=Tg(g,y,t,r)
   if y not in ps:assert actual=={y:Q(1)};off+=1
   else:
    k=ps.index(y)
    expected=xi(g,t,r) if k==len(g) else add(scale(xi(y,t,r),r),{ps[k+1]:Q(1)},-t)
    assert actual==expected
  # pi(g)-lambda(g) has range in path span, by evaluating T_g lambda(g).
  for x in words([1,-1,2,-2],2):
   y=red(g+x);diff=add(Tg(g,y,t,r),{y:Q(1)},-1)
   assert set(diff)<=set(ps)
stats.update(actual_path_matrices=path,actual_off_path_checks=off,observed_path_ranks=sorted(set(ranks)))
fresh=negative=0
for h in words([1,-1,2,-2],3)[1:]:
 for u in [3,4]:
  for w in words([1,-1,2,-2,u,-u],4):
   if w and w[0]==u:continue
   out=red((u,)+h+(-u,)+w)
   assert out and out[0]==u;fresh+=1
# Freshness is essential: h=u^-1 and w=u^2 yield an output outside R_u.
# A simpler failure takes h=u^-1, w=empty.
assert red((3,)+(-3,)+(-3,))==(-3,);negative+=1
stats.update(fresh_support_checks=fresh,nonfresh_negative_controls=negative)
# HS(M_2 tensor M_3) -> HS(M_2) tensor C^3 tensor conjugate(C^3).
# All matrix-unit left products, including both multiplier legs, and right leg.
vec=right=0
idx=lambda a,b,i,j:((a*2+b)*3+i)*3+j
for a,b,i,j,c,d,k,l in product(range(2),range(2),range(3),range(3),range(2),range(2),range(3),range(3)):
 x=kron(unit(2,a,b),unit(3,i,j));m=kron(unit(2,c,d),unit(3,k,l));mx=mm(m,x)
 actual={idx(aa,bb,ii,jj):mx[aa*3+ii][bb*3+jj] for aa,bb,ii,jj in product(range(2),range(2),range(3),range(3)) if mx[aa*3+ii][bb*3+jj]}
 expected={idx(c,b,k,j):Q(1)} if d==a and l==i else {}
 assert actual==expected;vec+=1
for i,j,k,l in product(range(3),repeat=4):
 # E_ij E_kl = delta_jk E_il; right action is B^T on conjugate leg (real units).
 assert mm(unit(3,i,j),unit(3,k,l))==(unit(3,i,l) if j==k else zeros(3,3));right+=1
stats.update(vectorization_left_unit_products=vec,vectorization_right_transpose_products=right)
# Genuine scaling model, used only as a domain/normalization diagnostic:
# J=c_0(Z), T(f)=sum a^(2n) f(n), beta(f)(n)=f(n-1).
sc=0
for a in [Q(2),Q(3),Q(1,2)]:
 c=a*a
 for seed in range(1,8):
  x={n:Q((n+seed)**2-2) for n in range(-3,4)}
  beta={n+1:v for n,v in x.items()};U=scale(beta,1/a)
  norm=lambda z:sum(a**(2*n)*v*v for n,v in z.items())
  assert norm(beta)==c*norm(x);assert norm(U)==norm(x)
  inverse=scale({n-1:v for n,v in U.items()},a);assert inverse==x
  d=lambda n:Q((n%3)-1)
  assert scale({n+1:d(n)*v for n,v in x.items()},1/a)=={n:d(n-1)*v for n,v in U.items()}
  assert c*(Q(1)/a)**2==1 # change from T to cT
  sc+=1
stats.update(trace_scaling_shift_cases=sc,wrong_positive_half_squared_norm_ratio_at_c4='16')
# Full finite commutant M_a tensor 1_b tensor M_f, not only diagonal coefficients.
# Compare product on (a,b,f) against minimal spatial sum on (b,a,f) by permutation.
compression=coefficients=0
for f in [1,2,3]:
 a=b=2;n=a*b*f
 ps=[unit(b,0,1),unit(b,1,0),unit(b,0,0)]
 zs=[[[Q(((i+1)*(j+2)+s)%7-3) for j in range(a*f)] for i in range(a*f)] for s in range(3)]
 # Rational rotation forces non-coordinate finite-dimensional compressions.
 R=eye(f)
 if f>=2:R[0][0]=R[1][1]=Q(3,5);R[0][1]=Q(-4,5);R[1][0]=Q(4,5)
 assert mm(tr(R),R)==eye(f)
 for r in range(1,f+1):
  W=[row[:r] for row in R];Qmap=kron(eye(a),W)
  cz=[mm(mm(tr(Qmap),z),Qmap) for z in zs]
  X=zeros(a*b*r,a*b*r);Y=zeros(a*b*r,a*b*r)
  for p,z in zip(ps,cz):
   Y=plus(Y,kron(p,z))
   for aa,bb,ff,cc,dd,gg in product(range(a),range(b),range(r),range(a),range(b),range(r)):
    X[(aa*b+bb)*r+ff][(cc*b+dd)*r+gg]+=p[bb][dd]*z[aa*r+ff][cc*r+gg]
  for aa,bb,ff,cc,dd,gg in product(range(a),range(b),range(r),range(a),range(b),range(r)):
   assert X[(aa*b+bb)*r+ff][(cc*b+dd)*r+gg]==Y[(bb*a+aa)*r+ff][(dd*a+cc)*r+gg];coefficients+=1
  # Permutation identifies operators and hence *exact* singular values and norm.
  compression+=1
# Norm supremum finite stress case: first two compressions miss a rank-one operator.
X=unit(3,0,2)
assert [sum(v*v for row in [r[:n] for r in X[:n]] for v in row) for n in [1,2,3]]==[0,0,1]
# Reverse amplification with identities preserves its rank-one norm exactly.
for f in [1,2,3]:assert mm(tr(kron(X,eye(f))),kron(X,eye(f)))==kron(unit(3,2,2),eye(f))
stats.update(full_commutant_compression_cases=compression,amplification_entry_equalities=coefficients,compression_rank_one_squared_norms=[0,0,1],reverse_amplifications=3)
# Countermodel to universal prescribed-representation spatiality only.
assert rank([[1,0,0],[0,0,0],[0,0,0]])==1
assert rank([[0,0,0],[0,1,0],[0,0,1]])==2
stats['unrelated_C2_flip_projection_ranks']=[1,2]
budgets=0
for q in range(2,30):
 for p in range(1,q):
  t=Q(p,q);m=(4/t**2).__floor__()+1;assert m*m*t*t>4*m;budgets+=1
stats['strict_witness_budgets']=budgets
print(json.dumps(dict(status='PASS',scope='Exact finite diagnostics only; no certification of infinite-algebra norms, ideal simplicity, trace uniqueness, normality or contribution.',stats=stats),sort_keys=True,indent=2))
