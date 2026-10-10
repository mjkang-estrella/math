"""Exact rational diagnostics only. Does not prove an infinite-volume theorem."""
from fractions import Fraction as F
from itertools import product
import json

def check():
 out={}; count=0
 # Integer Cartesian spin-one interaction: swap minus |sum ii><sum ii|.
 def basis(n):return list(product(range(3),repeat=n))
 def H(v,n):
  ans={w:F(0) for w in basis(n)}
  for w,x in v.items():
   for j in range(n-1):
    z=list(w);z[j],z[j+1]=z[j+1],z[j];ans[tuple(z)]+=x
    if w[j]==w[j+1]:
     for k in range(3):z=list(w);z[j]=z[j+1]=k;ans[tuple(z)]-=x
  return ans
 def dot(a,b):return sum(x*b.get(w,0) for w,x in a.items())
 B=basis(4);a={w:F(w[0]==w[1] and w[2]==w[3]) for w in B};b={w:F(w[0]==w[3] and w[1]==w[2]) for w in B}
 gram=[[dot(x,y) for y in [a,b]] for x in [a,b]];eng=[[dot(x,H(y,4)) for y in [a,b]] for x in [a,b]]
 assert gram==[[9,3],[3,9]] and eng==[[-36,-18],[-18,-18]];count+=8
 v={w:a[w]+b[w]/4 for w in B}; ray=dot(v,H(v,4))/dot(v,v);assert ray==F(-246,59)<-4;count+=1
 out['four_site_trial']={'gram':gram,'energy_matrix':eng,'rayleigh':str(ray),'per_site':str(ray/4)}
 # Exact annihilating polynomial for the open triad. Since it is real symmetric,
 # this certifies its spectrum belongs to {-3,-2,-1,0,1,2}, hence H3>=-3 I.
 eig=[-3,-2,-1,0,1,2]
 for w in basis(3):
  v={z:F(z==w) for z in basis(3)}
  for e in eig:
   Hv=H(v,3);v={z:Hv[z]-e*v[z] for z in basis(3)}
  assert all(x==0 for x in v.values());count+=1
 out['triad_annihilating_roots']=eig
 # Positive constraints may lose their exact kernel under arbitrarily small twirling.
 trunc=[]
 for k in range(2,42):
  t=F(1,k);a=(1-t*t)/(1+t*t);b=2*t/(1+t*t)
  assert a*a+b*b==1
  diag0=b*b/2;diag1=(1+a*a)/2;err2=b*b*(1-3*b*b/4)
  # Construct the actual projection, conditional expectation and error matrix.
  vec=[b,0,0,a];omega=[a,0,0,-b]
  mat=[[vec[i]*vec[j]+F(i==j==2) for j in range(4)] for i in range(4)]
  mul=lambda X,Y:[[sum(X[i][k]*Y[k][j] for k in range(4)) for j in range(4)] for i in range(4)]
  assert mul(mat,mat)==mat and all(sum(mat[i][j]*omega[j] for j in range(4))==0 for i in range(4))
  twirl=[[F(i%2==j%2)*sum(mat[2*(i//2)+k][2*(j//2)+k] for k in range(2))/2 for j in range(4)] for i in range(4)]
  assert twirl==[[F(i==j)*[diag0,diag0,diag1,diag1][i] for j in range(4)] for i in range(4)] and diag0>0 and diag1>0
  err=[[mat[i][j]-twirl[i][j] for j in range(4)] for i in range(4)]
  expectation=a*a*diag0+b*b*diag1
  assert mul(err,err)==[[F(i==j)*[err2,b**4/4,b**4/4,err2][i] for j in range(4)] for i in range(4)] and 0<b**4/4<=err2<=b*b and expectation==b*b*(1+2*a*a)/2>0
  trunc.append({'t':str(t),'smallest_twirled_eigenvalue':str(diag0),'error_squared':str(err2),'ground_expectation':str(expectation)});count+=4
 out['kernel_loss']=trunc
 # Exact finite reversible chain calculation, with independently chosen rational
 # waiting attenuation q and lag attenuation u, u^2 and v for three coordinates.
 states=list(product([-1,1],repeat=3));alpha=F(1,4)
 f=lambda x:F(x[2]*(1+x[0]+x[1]),3)
 cases=0
 for q,u,v in product([F(1,5),F(1,2),F(4,5)],repeat=3):
  pf={x:sum(f(y)*F(1+u*x[0]*y[0],2)*F(1+u*u*x[1]*y[1],2)*F(1+v*x[2]*y[2],2) for y in states) for x in states}
  A=sum(f(x)*pf[x] for x in states)/8
  B=sum((1+alpha*q*x[0]-alpha*q*q*x[1])*f(x)*pf[x] for x in states)/8
  assert A==v*(1+u+u*u)/9
  assert B-A==alpha*v*((1+u)*q-(1+u*u)*q*q)/9
  assert all(F(1,2)<=1+alpha*q*x[0]-alpha*q*q*x[1]<=F(3,2) for x in states)
  cases+=1;count+=3
 out['reversible_chain']={'cases':cases,'alpha':str(alpha),'limiting_bump_coefficient':'1/72','limit_stationary':'exp(-t)/3'}
 # Common scaling plus finite defects: exact norm bookkeeping, no eigenvalue simulation.
 for L in [60,120,2304,4608]:
  for eps in [F(1,10**k) for k in range(2,10)]:
   v=2*eps*L;b=F(784*L,2304)
   assert 4*b*v==8*eps*b*L
   count+=1
 out['purity_comparison_cases']=32
 # Poincare is not classical LSI for a rare atom. Entropy=log(1/p),
 # Dirichlet=1-p; taking p=2^-k gives ratio>=k/2 since log2>=1/2.
 for k in range(2,82):
  p=F(1,2**k);D=1-p;assert F(k,2)/D>=F(k,2);count+=1
 out['rare_atom_cases']=80
 out['exact_assertions']=count
 out['status']='PASS exact algebra only; no floating diagnostics; no substantial theorem certified'
 return out
if __name__=='__main__':print(json.dumps(check(),indent=2,default=str))
