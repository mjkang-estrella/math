"""Finite exact instances only. No universal or substantiality certification."""
from fractions import Fraction as Q
from math import isqrt,lcm

def check():
 weights=[Q(1,10),Q(2,10),Q(3,10),Q(4,10)]
 vals=[(Q(1),Q(2)),(Q(-2),Q(1)),(Q(3),Q(-1)),(Q(0),Q(2))]
 cells=[[0,1],[2,3]]
 norm=lambda x:sum(t*t for t in x)
 mean=lambda ids:tuple(sum(weights[i]*vals[i][j] for i in ids)/sum(weights[i] for i in ids) for j in range(2))
 full=sum(weights[i]*norm(vals[i]) for i in range(4));projected=Q(0);residual=Q(0)
 for ids in cells:
  m=mean(ids);q=sum(weights[i] for i in ids);projected+=q*norm(m)
  residual+=sum(weights[i]*norm(tuple(vals[i][j]-m[j] for j in range(2))) for i in ids)
 assert full==projected+residual
 sign_avg=Q(0)
 for e in [-1,1]:
  for f in [-1,1]:
   z=tuple(sum(weights[i]*vals[i][j]*(e if i<2 else f) for i in range(4)) for j in range(2));sign_avg+=norm(z)/4
 rhs=sum(norm(tuple(sum(weights[i]*vals[i][j] for i in ids) for j in range(2))) for ids in cells)
 assert sign_avg==rhs
 # gamma>3 gives two strictly negative exponents with inverse masses retained.
 gamma=Q(7,2);k=Q(8,5);e=Q(1,10)
 assert e+2*k-gamma<0 and 3-2*k<0
 # Exact frozen saturation, including diagonal atoms.
 points=[Q(0),Q(1,128),Q(1,64)];theta=Q(1,8)
 K=lambda x,y:min(1/theta,1/abs(x-y)) if x!=y else 1/theta
 assert sum(K(x,y) for x in points for y in points)/9==1/theta
 # Disjoint cycles retain each band's ranks at every phase.
 bands=[[0,1,2],[4,5,6,7]];swaps=[(0,1),(1,2),(4,5),(5,6),(6,7)]
 labels=list(range(8));hist={i:[] for b in bands for i in b}
 for _ in range(lcm(3,4)):
  for i in hist:hist[i].append(labels.index(i))
  for a,b in swaps:labels[a],labels[b]=labels[b],labels[a]
 for band in bands:
  for i in band:
   assert set(hist[i])==set(band)
   assert len({hist[i].count(z) for z in band})==1
 # Concrete exact finite prefix of sparse growth bands; square-root constant bounded rationally.
 # a=9/10, sqrt(C*)=101/100, theta=6/5, c=6/5.
 def sum_t(n):return Q(n*(n+1),2)
 def sum_t2(n):return Q(n*(n+1)*(2*n+1),6)
 results=[];degree=100
 for _ in range(3):
  L=isqrt(degree);M=(6*degree)//5;D=(M+1)**2-(L+1)**2
  numerator=2*(sum_t2(M+1)-sum_t2(L+1))-(sum_t(M+1)-sum_t(L+1))
  avg=Q(101,90)*numerator/D
  assert D>Q(6,5)*(degree+1)**2 and avg<degree
  results.append(dict(k=degree,L=L,M=M,D=D,mean_bound=str(avg)))
  next_degree=(M+2)**2;assert isqrt(next_degree)>M;degree=next_degree
 # Exact harmonic-series lower bound for a finite sample supported in degrees >= k+1.
 for degree in [1,2,5]:
  for r in [Q(1),Q(2),Q(5)]:
   coeff=[Q(1,4),Q(3,4)]
   energy=sum(c*r**(2*(degree+1+i)) for i,c in enumerate(coeff))
   assert energy>=r**(2*degree+2)
   assert r**(degree+1)/(1+r)**degree>=r/2**degree
 return dict(status='PASS finite exact instances only',variance=str(full),inverse_mass_projection=str(projected),sign_average=str(sign_avg),shell_exponents=[str(e+2*k-gamma),str(3-2*k)],frozen_diagonal_kernel=str(1/theta),finite_band_prefix=results,scope='No universal Hilbert, Fourier, incidence, dimension, PDE, geometry, external-paper or contribution certification.')
if __name__=='__main__':
 import json
 print(json.dumps(check(),indent=2))
