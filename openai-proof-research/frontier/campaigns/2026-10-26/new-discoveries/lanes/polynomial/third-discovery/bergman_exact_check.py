from pathlib import Path
import sys,math,json,hashlib
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'.pydeps'))
from flint import fmpz_poly
z=fmpz_poly([0,1])
def Q_source(m,n):
 k=m-n;p=m*m*z**k
 for j in range(m-1):
  L=(1+n*(j+1)+m-1)//m
  kap=m+n-1+n*j-m*L
  p+=(j+1)*(kap+1)*z**(j-L+1)
  p+=(j+1)*(m-kap-1)*z**(j-L+2)
  p+=(m-j-1)*(kap+1)*z**(j+m-n-L+1)
  p+=(m-j-1)*(m-kap-1)*z**(j+m-n-L+2)
 return p

def A(m,n,r):
 c=[0]*(m-n+1)
 for p in range(m):c[p-(n*p+r)//m]+=1
 return fmpz_poly(c)

def sos(m,n):
 k=m-n;R=fmpz_poly([0])
 for r in range(m):
  p=A(m,n,r);c=list(p);d=len(c)-1
  R+=z**(k-d)*p*fmpz_poly(c[::-1])
 return R

def Q_D(m,n):
 k=m-n;p=fmpz_poly([0]);D=lambda r:min(r+1,2*m-1-r)
 for r in range(2*m-1):
  for q in range(2*m-1):
   if (q-n*r-n+1)%m==0:
    e=(k*r+q-n+1)//m
    assert 0<=e<=2*k
    p+=D(r)*D(q)*z**e
 return p

if __name__=='__main__':
 cases=0
 for m in range(2,81):
  for n in range(1,m):
   if math.gcd(m,n)!=1:continue
   p=Q_source(m,n);s=sos(m,n);assert p==s,(m,n,'sos')
   if m<=25:assert p==Q_D(m,n),(m,n,'D')
   pp=next(p for p in range(1,m)if(n*p)%m==m-1);q=(n*pp-m+1)//m
   assert pp-q>=1
   assert A(m,n,1)-A(m,n,0)==z**(pp-q-1)*(1-z),(m,n,'difference')
   assert p.degree()==2*(m-n) and p[0]>0
   cases+=1
 print(json.dumps({'status':'PASS','coprime_pairs':cases,'m_max':80,'D_formula_m_max':25,'checks':['literal_source_q0_to_q4_EQUALS_finiteSOS','A1_minus_A0_monomial_identity','source_degree_and_nonzero_constant'],'arithmetic':'exact Python integers and FLINT integer polynomials'},indent=2))
