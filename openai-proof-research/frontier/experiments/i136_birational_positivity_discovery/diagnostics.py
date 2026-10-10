"""New finite checks only. Pure, offline, no files/subprocesses/network."""
from fractions import Fraction as F
from itertools import product
from math import comb

def multi(d,m):
 return [x for x in product(range(m+1),repeat=d) if sum(x)<=m]
def rank_mod(a,p):
 a=[list(x) for x in a]; row=0
 for col in range(len(a[0])):
  pivot=next((j for j in range(row,len(a)) if a[j][col]%p),None)
  if pivot is None:continue
  a[row],a[pivot]=a[pivot],a[row];inv=pow(a[row][col]%p,-1,p)
  a[row]=[(x*inv)%p for x in a[row]]
  for j in range(len(a)):
   if j!=row:
    c=a[j][col];a[j]=[(x-c*y)%p for x,y in zip(a[j],a[row])]
  row+=1
  if row==len(a):break
 return row

def run():
 jets=[]
 for n,m,prime in [(2,[0,1],5),(2,[1,3,2],5),(3,[2,1],5),(3,[1,2,0],7),(2,[4],2),(3,[3],3)]:
  cols=[]
  for beta in multi(n-1,max(m)):
   h=sum(max(z+1-sum(beta),0) for z in m)
   cols.extend([beta+(j,) for j in range(h)])
  rows=[]
  for i,mi in enumerate(m):
   c=i+1
   for alpha in multi(n,mi):
    rr=[]
    for e in cols:
     value=1
     for j in range(n):
      if alpha[j]>e[j]:value=0;break
      value=value*comb(e[j],alpha[j])*pow(c if j==n-1 else 1,e[j]-alpha[j],prime)%prime
     rr.append(value)
    rows.append(rr)
  wanted=sum(comb(mi+n,n) for mi in m)
  assert len(cols)==len(rows)==wanted
  assert rank_mod(rows,prime)==wanted
  jets.append(dict(n=n,orders=m,characteristic=prime,rank=wanted))
 containment=0
 for n in [2,3,4]:
  a=F(1,4);b=1/a**(n-1);w=[F(1,10),F(3,20),F(1,20)];S=sum(w);M=max(w)
  for k in [20,40,100]:
   m=[int(k*z) for z in w];maxm=max(m)
   H=lambda t:sum(max(z+1-t,0) for z in m)
   bound=max(M/a,S/b)+F(len(w),k)/b
   for t in range(maxm+1):
    assert F(t,k)/a+F(H(t),k)/b<=bound
    containment+=1
 tau=F(99,100)
 assert tau**3<1 and F(4,3)*tau**3>1
 assert 125<128 and tau**3*81>64
 # Cubed support inequality for each integral q; V=N scaling removed.
 dual_instances=0
 for N in [1,2,3,10,100]:
  for q in range(1,2*N+1):
   sy=4*q if q<=N else q+3*N
   assert sy**3<=64*N*N*q
   dual_instances+=1
 # Layer reconstruction with a nontrivial q0 plateau, before root-weight cost.
 w=[F(9,20),F(2,5),F(1,3),F(1,5),F(1,10)];q0=2
 z=[w[0]]*q0+w[q0:];ext=w+[F(0)]
 layers={q0:w[0]-ext[q0]}
 layers.update({q:ext[q-1]-ext[q] for q in range(q0+1,len(w)+1)})
 assert [sum(v for q,v in layers.items() if i<q) for i in range(len(w))]==z
 assert all(a<=b for a,b in zip(w,z))
 # Telescoping recurrence, including the terminal error and empty product.
 kap=[F(1,2),F(2,3),F(3,4)];err=[F(1,7),F(1,11),F(1,13)];terminal=F(2,5)
 d=terminal
 for q,e in reversed(list(zip(kap,err))):d=e+q*d
 prod=F(1);rhs=F(0)
 for q,e in zip(kap,err):rhs+=prod*e;prod*=q
 assert d==rhs+prod*terminal
 counts=[]
 for aa in [F(1,2),F(4,9),F(9,16)]:
  for k in range(41):
   ll=max(l for l in range(k+1) if l*(l+1)<=aa*k*(k+1))
   assert k==0 and ll==0 or k>=1 and ll<=k-1
   counts.append((str(aa),k,(ll+1)**2))
 residuals=0
 for ell in range(1,10):
  for r in [F(1),F(2),F(10)]:
   f=F(2,3)*r+F(1,3);fp=F(2,3)
   residual=ell*r**(ell-2)*((ell-1)*f*f+2*r*f*fp-(ell+1)*r*r)
   assert residual<=0;residuals+=1
 for k in range(10):
  for ell in range(k+1,k+8):
   assert F(3,2*ell+3)<=F(3,2*k+5)
  for r in [F(1),F(2),F(10)]:assert r**(k+1)/(1+r)**k>=r/2**k
 return dict(status='PASS',mixed_jet_ranks=jets,diagram_instances=containment,dual_instances=dual_instances,radial_residual_instances=residuals,limiting_mode_instances=len(counts),I5='Counterexample proved in report; zero differences do not bound the starting function',scope='Finite instances only; not universal proof, significance, or priority certification')
if __name__=='__main__':
 import json
 print(json.dumps(run(),indent=2))
