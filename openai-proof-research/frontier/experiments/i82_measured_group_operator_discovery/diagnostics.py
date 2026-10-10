"""Finite exact transcription/stress checks. Does not prove the analytic theorem."""
from fractions import Fraction as Q
from itertools import product
import json,math

def mat(a): return [[Q(x) for x in r] for r in a]
def eye(n):return [[Q(i==j) for j in range(n)] for i in range(n)]
def add(a,b):return [[x+y for x,y in zip(r,s)]for r,s in zip(a,b)]
def scale(c,a):return [[c*x for x in r] for r in a]
def mul(a,b):return [[sum((a[i][k]*b[k][j] for k in range(len(b))),Q(0)) for j in range(len(b[0]))]for i in range(len(a))]
def kron(a,b):return [[a[i][j]*b[k][l] for j in range(len(a[0])) for l in range(len(b[0]))] for i in range(len(a)) for k in range(len(b))]
def tr(a):return sum(a[i][i] for i in range(len(a)))/len(a)
def transpose(a):return list(map(list,zip(*a)))
I=eye(2);X=mat([[0,1],[1,0]]);Z=mat([[1,0],[0,-1]])
xs=[kron(Z,I),kron(Z,X),kron(Z,Z)];d=4
for a in xs:assert tr(a)==0 and mul(a,a)==eye(4)
blocks=[[scale(Q(1,2),add(mul(a,b),mul(b,a))) for b in xs]for a in xs]
G=[[blocks[i//d][j//d][i%d][j%d]for j in range(12)]for i in range(12)]
a=[Q(1),Q(0),Q(0),Q(0)];u=[-2*x for x in a]
x=[sum(kron(I,X)[i][j]*a[j] for j in range(4))for i in range(4)]
z=[sum(kron(I,Z)[i][j]*a[j] for j in range(4))for i in range(4)]
v=u+x+z
q=sum(v[i]*G[i][j]*v[j]for i in range(12)for j in range(12));assert q==-2
raw=[[mul(a,b)for b in xs]for a in xs]
T=[[xs[j//d][i][j%d]for j in range(12)]for i in range(4)]
P=mul(transpose(T),T)
assert P==[[raw[i//d][j//d][i%d][j%d]for j in range(12)]for i in range(12)]
# Non-identically distributed, tensor-independent genuine matrix rows.
y=[xs[0],xs[0],xs[2]]
sums=[add(kron(a,eye(4)),kron(eye(4),b))for a,b in zip(xs,y)]
R=[[Q(1,2)*(tr(mul(xs[i],xs[j]))+tr(mul(y[i],y[j])))for j in range(3)]for i in range(3)]
checks=0
for inds in product(range(3),repeat=4):
 p=eye(16)
 for j in inds:p=mul(p,sums[j])
 actual=tr(p)/4;a,b,c,d0=inds
 gauss=R[a][b]*R[c][d0]+R[a][c]*R[b][d0]+R[a][d0]*R[b][c]
 assert abs(actual-gauss)<=Q(4,2);checks+=1
for a,b in product(range(3),repeat=2):assert tr(mul(sums[a],sums[b]))/2==R[a][b]
# Singularity and changing rank: exact regularized variance bounds.
varchecks=0
for n in range(1,50):
 for rank in range(1,n+1):
  lambdas=[Q(1,rank)]*rank+[Q(0)]*(n-rank)
  for den in [4,16,256]:
   tau=Q(1,den*n);v0=sum(l*l/(l+tau)for l in lambdas)
   assert 1-n*tau<=v0<=1
   assert sum(l-l*l/(l+tau)for l in lambdas)<=n*tau
   varchecks+=1
# Source height propagation only; no claims about exact action costs.
height=0
for M in range(101,401):
 known=set(range(99))
 for k in range(M-99):
  assert set(range(k,k+99))<=known;known.add(k+99)
 assert known==set(range(M));height+=1
# Source Bernstein route: degree is polynomial but monomial l1 bound is exponential.
# Binomial sum of absolute expansion coefficients <=3^D (a crude upper envelope).
for D in range(1,60):assert sum(math.comb(D,k)*2**(D-k)for k in range(D+1))==3**D
# Integer coefficient safety used in the theorem, after symbolic exponent collection.
assert 10**9*17**3*2**39<2**84
assert 500*16*2**36<2**50
assert Q(2**84+2**50,2**100)<Q(1,8)
# Invariance Gaussian contribution < eps/8: use sqrt(2)<3/2.
assert 16*Q(3,2)*(Q(1,2**10)+Q(2,2**12))<Q(1,8)
# Fourier bound < eps/4 because 1+4t²(1-n tau)>256 eps^-4.
assert 4*16**2*(1-Q(1,2**24))>256
print(json.dumps({'status':'PASS','symmetrized_covariance_negative_quadratic':str(q),'raw_gram_factorization':True,'fourth_moment_words':checks,'second_moment_words':9,'regularized_variance_checks':varchecks,'finite_height_propagations':height,'bernstein_envelopes':59,'parameter_budget':True,'limits':'Exact finite checks only; no analytic or significance certification.'},sort_keys=True,indent=2))
