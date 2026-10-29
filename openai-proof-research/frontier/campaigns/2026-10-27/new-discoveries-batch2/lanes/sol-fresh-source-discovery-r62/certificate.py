from fractions import Fraction as Q
from math import factorial,comb
from pathlib import Path
import json
P=Path(__file__).resolve().parent
# Independent construction: (z^2+5z+6)^N and (z^2+5z+4)^N.
def power(c,N):
 v=[1]
 for _ in range(N):
  w=[0]*(len(v)+2)
  for k,x in enumerate(v):
   for j,y in enumerate((c,5,1)):w[k+j]+=x*y
  v=w
 return v
out={}
for N in (35,100):
 A,B=power(6,N),power(4,N)
 dif=[B[k+1]*A[k]-B[k]*A[k+1] for k in range(2*N)]
 assert all(d>=0 for d in dif)
 (P/f'hypotheses-{N}.json').write_text(json.dumps(dict(N=N,A=A,B=B,adjacent_determinants=dif),indent=2))
 d=2*Q(35,99)**N-Q(1,3)**N-Q(9,25)**N
 assert d<0
 # alternate unreduced common numerator
 num=2*875**N-825**N-891**N
 assert d==Q(num,2475**N) and num<0
 out[str(N)]={'condition13':True,'delta1':str(d),'integer_numerator':num,'denominator_base':2475}
# Actual log-concavity refutation, full entire function and derivatives.
N=100;t=Q(1);x=Q(5,6)**N;M=10
F=Fp=Fpp=Q(0)
for n in range(M+1):
 z=t+n
 g=((z+1)/(z+3))**N
 u=Q(2)/((z+1)*(z+3))
 up=-Q(4)*(z+2)/((z+1)**2*(z+3)**2)
 w=x**n/factorial(n)
 F+=g*w;Fp+=N*u*g*w;Fpp+=(N*N*u*u+N*up)*g*w
T=x**(M+1)/(factorial(M+1)*(1-x))
# all t>=1: 0<g<=1, |g'|<=N/4, |g''|<=N^2/16+3N/16
E0=T;E1=Q(N,4)*T;E2=Q(N*N+3*N,16)*T
assert F-E0>0 and Fpp-E2>0
lower=(F-E0)*(Fpp-E2)-(Fp+E1)**2
assert lower>0
# Convenient small readable rational lower bound, scaled by 4^N.
assert lower*4**N>1
out['curvature']={'N':N,'mu':1,'x':'(5/6)^100','M':M,'certified_4powerN_times_curvature_lower_bound':'>1','F':str(F),'Fp':str(Fp),'Fpp':str(Fpp),'tail_T':str(T),'lower':str(lower)}
(P/'certificate.json').write_text(json.dumps(out,indent=2));print('PASS: condition13 at N35/N100; negative literal coefficients; full analytic curvature >4^-100 at N100')
