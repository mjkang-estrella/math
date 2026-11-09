"""Finite exact diagnostics for failed mechanisms; no MathDB theorem certificate."""
from fractions import Fraction
from math import isqrt
import json

def reduce(w):
 out=[]
 for x in w:
  if out and out[-1]==-x:out.pop()
  else:out.append(x)
 return out

def inv(w):return [-x for x in w[::-1]]
def conjugate(n):return ([2]*n if n>=0 else [-2]*(-n))+[1]+([-2]*n if n>=0 else [2]*(-n))
print('Effective-coherence obstruction: alpha=conjugation by b; H=<a,t>, t=b*z in F(a,b) x Z.')
for n in range(9):
 words=[conjugate(j) for j in range(-n,n+1)]
 assert len({tuple(reduce(w)) for w in words})==2*n+1
 print(json.dumps(dict(n=n,schreier_generators=2*n+1,max_word_length=max(map(len,words)),last_positive=conjugate(n))))
print('These are diagnostic encodings. Infinite-rank conclusion uses the ordinary free-reduction proof in MATHEMATICAL-ATTEMPTS.md.')
print('Delone anisotropic lattices diag(1,L,L,L) Z^4: r=1/2, R^2=(1+3L^2)/4.')
for L in [2,3,8,32,128]:
 print(json.dumps(dict(L=L,r=str(Fraction(1,2)),R_squared=str(Fraction(1+3*L*L,4)),ratio_squared=1+3*L*L,rank_of_unit_step_component=1,minimum_step_for_full_rank=L)))
print('Quantum partial enumeration: exact sum comparison without floating point. For m<=k/2 each remaining k-j >=k/2, hence sum<=m sqrt(2N/k); see notes for scope/prior restriction.')
