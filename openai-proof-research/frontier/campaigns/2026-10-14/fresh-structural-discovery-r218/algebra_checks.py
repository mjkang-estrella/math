"""Exact rational checks of polynomial identities; standard library only.
The invariant-form identities are linear in A,B and degree <=3 in a.
The two basis choices (A,B) and four distinct a values therefore certify
these identities by polynomial interpolation. Positivity/limits are proved
in the author proof, not inferred from this check.
"""
from fractions import Fraction as Q

def mat(rows): return [[Q(x) for x in row] for row in rows]
def tr(M): return [list(x) for x in zip(*M)]
def mm(M,N): return [[sum(M[i][k]*N[k][j] for k in range(4)) for j in range(4)] for i in range(4)]
def plus(M,N): return [[M[i][j]+N[i][j] for j in range(4)] for i in range(4)]
def scale(t,M): return [[t*x for x in row] for row in M]
I=mat([[0,-1,0,0],[1,0,0,0],[0,0,0,-1],[0,0,1,0]])
K=mat([[0,0,-1,0],[0,0,0,1],[1,0,0,0],[0,-1,0,0]])
Id=mat([[int(i==j) for j in range(4)] for i in range(4)])
zero=mat([[0]*4 for _ in range(4)])
assert mm(I,I)==scale(-1,Id) and mm(K,K)==scale(-1,Id)
assert plus(mm(I,K),mm(K,I))==zero
for A,B in [(Q(1),Q(0)),(Q(0),Q(1))]:
 for a in map(Q,[-2,-1,0,1]):
  L=plus(I,scale(a,K));cross=a*(A+B)
  O=mat([[0,A,cross,0],[-A,0,0,0],[-cross,0,0,B],[0,0,-B,0]])
  assert mm(tr(L),L)==scale(1+a*a,Id)
  assert mm(mm(tr(L),O),L)==scale(1+a*a,O)
  assert mm(O,L)==tr(mm(O,L))
  pf=O[0][1]*O[2][3]-O[0][2]*O[1][3]+O[0][3]*O[1][2]
  assert pf==A*B
print('Quaternionic identities and invariant-form polynomial identities checked exactly; eight rational basis/node cases, with stated degree bounds. No numerical approximation.')
