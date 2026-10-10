"""Finite exact checks only. No analytic coercivity or P112 certification."""
import sys
sys.dont_write_bytecode=True
from fractions import Fraction as F
from math import comb,factorial
import json

def mm(a,b):return [[sum(a[i][k]*b[k][j] for k in range(len(b))) for j in range(len(b[0]))] for i in range(len(a))]
def adj(a):return [[a[j][i].conjugate() for j in range(len(a))] for i in range(len(a[0]))]
def sub(a,b):return [[x-y for x,y in zip(u,v)] for u,v in zip(a,b)]
def derivative(p,i):
 q={}
 for a,c in p.items():
  if a[i]:
   b=list(a);b[i]-=1;q[tuple(b)]=c*a[i]
 return q

def plus(p,q):
 d=p.copy()
 for a,c in q.items():d[a]=d.get(a,0)+c
 return {a:c for a,c in d.items() if c}
def df(n):
 z=1
 for i in range(n,0,-2):z*=i
 return z
def moment(a):
 if any(i%2 for i in a):return F(0)
 return F(df(a[0]-1)*df(a[1]-1)*df(a[2]-1),df(sum(a)+1))
def check():
 # Gaussian integer entries are exactly representable here; all products stay small integers.
 J=[[-1+0j,-1j],[-1j,1+0j]];zero=[[0j,0j],[0j,0j]]
 assert mm(J,J)==zero
 C=sub(mm(adj(J),J),mm(J,adj(J)))
 assert C==[[0j,4j],[-4j,0j]]
 assert mm(C,[[1],[1j]])==[[-4],[-4j]]
 rational=[]
 for m,k in [(F(1),F(1)),(F(3),F(2)),(F(2),F(10)),(F(1),F(1,2))]:
  assert k>m/3
  a=k/(2*m+k);assert 0<a<1 and 1-a==2*m/(2*m+k)
  # Hermitian part eigenvalues and signed commutator eigenvalues, symbolically exact.
  rational.append({'m':str(m),'kappa':str(k),'accretivity':str(1-a),'commutator_eigenvalues':[str(-4*a*a),str(4*a*a)]})
 polys=[]
 for k in range(1,17):
  p={(k-j,j,0):comb(k,j)*(-1)**(j//2) for j in range(0,k+1,2)}
  lap={}
  for i in range(3):lap=plus(lap,derivative(derivative(p,i),i))
  assert not lap and not derivative(p,2)
  q=p
  for _ in range(k):q=derivative(q,0)
  assert q=={(0,0,0):factorial(k)}
  n=sum((F(c*d)*moment(tuple(a[i]+b[i] for i in range(3))) for a,c in p.items() for b,d in p.items()),F(0))
  assert n>0
  polys.append({'degree':k,'squared_unit_sphere_norm':str(n),'derivative_at_center':factorial(k)})
 return {'status':'PASS finite exact instances only','nilpotent_square_zero':True,'signed_commutator_eigenvalues_at_aq_one':[-4,4],'rational_symbol_cases':rational,'physical_polynomials':polys,'scope':'Finite symbol and polynomial identities; universal arguments are in the report; no uniform transfer bound, P112 or substantiality certification'}
if __name__=='__main__':print(json.dumps(check(),indent=2))
