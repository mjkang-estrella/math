#!/usr/bin/env python3
"""Exact bounded diagnostics, not a proof of either universal conjecture."""
import os, resource, signal, json, math, time
from fractions import Fraction
for key in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[key]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(40,)*2)
signal.alarm(55)
start=time.monotonic()
def counts(n,f):return [sum((f>>s)&1 for s in range(1<<n) if s.bit_count()==k) for k in range(n+1)]
def failures(n,a):
 return [k for k in range(1,n) if a[k]*a[k]*k*(n-k)<a[k-1]*a[k+1]*(k+1)*(n-k+1)]
def gap(n,f):
 sets=[s for s in range(1<<n) if (f>>s)&1];bad=[]
 for s in sets:
  for t in sets:
   if t.bit_count()<s.bit_count()+2:continue
   diff=t&~s
   if not any((diff>>x)&1 and (f>>(s|(1<<x)))&1 for x in range(n)):
    return [s,t]
 return None
# Every ideal of B_n decomposes uniquely as I0 + x_n I1 with I1 subset I0.
ideals=[0,1];ideal_rows=[];source_failures=[]
for n in range(1,6):
 shift=1<<(n-1)
 ideals=[a|(b<<shift) for a in ideals for b in ideals if b&~a==0]
 passed=0
 for f in ideals:
  if not f&1:continue
  if gap(n,f) is None:
   passed+=1;a=counts(n,f);bad=failures(n,a)
   if bad:source_failures.append(dict(n=n,family=f,counts=a,indices=bad))
 ideal_rows.append(dict(n=n,ideals=len(ideals),two_matroids=passed))
# Independent direct dependent-set enumeration, all labelled graphs through n=6.
graph_rows=[];graph_failures=[]
for n in range(2,7):
 edges=[(i,j) for i in range(n) for j in range(i+1,n)]
 total=0
 for g in range(1,1<<len(edges)):
  adj=[0]*n
  for k,(i,j) in enumerate(edges):
   if (g>>k)&1:adj[i]|=1<<j;adj[j]|=1<<i
  independent=[False]*(1<<n);independent[0]=True;ds=[0]*(n+1)
  for s in range(1,1<<n):
   low=s&-s;i=low.bit_length()-1;r=s^low
   independent[s]=independent[r] and not (adj[i]&r)
   if not independent[s]:ds[s.bit_count()]+=1
  bad=failures(n,ds)
  if bad:graph_failures.append(dict(n=n,graph=g,counts=ds,indices=bad))
  total+=1
 graph_rows.append(dict(n=n,graphs=total))
# CLC-route falsifier: co-dependent sets for edges {0,1},{2,3}.
n=4;E=[3,12];family=sum(1<<s for s in range(16) if any((15^s)&e==e for e in E))
assert family==sum(1<<s for s in [0,1,2,3,4,8,12])
assert gap(4,family) is None
assert counts(4,family)==[1,4,2,0,0] and not failures(4,[1,4,2,0,0])
# Q = d_y^2[y^4+y^3 sum x+y^2(x0*x1+x2*x3)].
# Q(1,1+t,1+t,1-t,1-t)=40+4t^2.
def actual_derivative_value(t):
 x=[1+t,1+t,1-t,1-t]
 result=Fraction(0)
 for mask in range(16):
  if not (family>>mask)&1:continue
  power=4-mask.bit_count()
  term=Fraction(power*(power-1))
  for j in range(4):
   if mask>>j&1:term*=x[j]
  result+=term
 return result
q0=actual_derivative_value(Fraction(0))
qp=actual_derivative_value(Fraction(1,2));qm=actual_derivative_value(Fraction(-1,2))
assert (qm,q0,qp)==(41,40,41) and q0*q0<qm*qp
qprime=(qp-qm)
qsecond=(qp+qm-2*q0)/Fraction(1,4)
q0,qprime,qsecond=map(int,(q0,qprime,qsecond))
assert q0*qsecond-qprime*qprime==320>0
result=dict(status='PASS' if not(source_failures or graph_failures) else 'TRIGGER',ideal_rows=ideal_rows,graph_rows=graph_rows,source_failures=source_failures,graph_failures=graph_failures,route_falsifier=dict(edges=E,family=[s for s in range(16) if family>>s&1],counts=counts(4,family),Q0=q0,Qprime=qprime,Qsecond=qsecond,log_second='1/5'),elapsed_seconds=time.monotonic()-start,maxrss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,limits=dict(address_space_bytes=512*1024**2,cpu_seconds=40,wall_seconds=55,blas_threads=1))
print(json.dumps(result,indent=2))
