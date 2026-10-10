"""New finite diagnostics only. No inherited module is imported or executed."""
from fractions import Fraction as F
from itertools import product

def run():
 exponents=[]
 for n in [5,7,11,13]:
  tau=F(1,4*n);gamma=F(1,32*n);a=F(1,128*n*n)
  assert 2*n*a<gamma and 2*n*a<F(5,16)
  for beta in [F(1,10),F(1,2),F(1),F(3)]:
   delta=tau/(4*(2*n+1/beta));eps=tau/(8*(1+1/beta))
   worst=-tau+(2*n+1/beta)*delta+(1+1/beta)*eps+tau/8
   assert worst==-tau/2
   exponents.append(dict(n=n,beta=str(beta),delta=str(delta),Q_shell_margin=str(gamma-2*n*a),q_error_exponent=str(worst)))
 local=[]
 for ell,n in [(3,5),(3,7),(5,5)]:
  # Unit-translate labels normalized by the first coordinate. All are distinct lines.
  labels=[(1,)+v for v in product(range(1,ell),repeat=n-1)]
  T=(ell-1)**(n-1);assert len(labels)==T
  x=(1,)*n;y=(2,)*n;z=(1,2)+(1,)*(n-2)
  def contained(v,label):
   return all(v[i]%ell==(v[0]*label[i])%ell for i in range(n))
  cx=sum(contained(x,l) for l in labels)
  cy=sum(contained(y,l) for l in labels)
  cxy=sum(contained(x,l) and contained(y,l) for l in labels)
  cxz=sum(contained(x,l) and contained(z,l) for l in labels)
  assert cx==cy==cxy==1 and cxz==0
  assert F(cxy,T)!=F(cx,T)*F(cy,T)
  # O=L in this explicit split example; additive index m=ell^(n-1).
  m=ell**(n-1);uR=F(ell-1,ell)**n;uO=F(ell-1,ell)
  assert m*uR/uO==T
  ambient=(ell**n-1)//(ell-1);assert ambient>n
  local.append(dict(ell=ell,n=n,index=m,labels=T,one_vector=str(F(cx,T)),proportional_pair=str(F(cxy,T)),nonproportional_pair=str(F(cxz,T)),independent_prediction=str(F(cx,T)*F(cy,T)),unit_ratio=str(m*uR/uO),torus_neighbors=n,ambient_neighbors=ambient))
 return dict(status='PASS',exact_exponent_checks=exponents,actual_split_local_module_checks=local,scope='Finite rational arithmetic and explicit finite local modules only; not universal mathematics, arithmetic counterexample, substantiality, acceptance, priority, human or formal certification.')
