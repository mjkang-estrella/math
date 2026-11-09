#!/usr/bin/env python3
import os
os.environ.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1')
import resource
resource.setrlimit(resource.RLIMIT_AS,(384*1024**2,384*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(90,90))
from fractions import Fraction as Q
import json,math
from pathlib import Path
P=Path(__file__).resolve().parent
out={'memory_cap_MiB':384,'cpu_cap_seconds':90,'blas_threads':1,'numerical_is_proof':False}
def sums(b,n):
 a=sum((Q(n,1)/(n*n-b*k*n+k*k) for k in range(1,n)),Q(0))
 return a+1/Q(n),a+1/((2-b)*n)
exact=[]
for b in [Q(3,4),Q(5,4),Q(7,4),Q(19,10),Q(199,100),Q(1999,1000)]:
 prev=sums(b,1);sg=[[],[]]
 for n in range(2,81):
  now=sums(b,n)
  for j in range(2):sg[j].append((now[j]>prev[j])-(now[j]<prev[j]))
  prev=now
 exact.append({'b':str(b),'n_max':80,'L_signs':sorted(set(sg[0])),'R_signs':sorted(set(sg[1]))})
out['exact_adjacent']=exact
# Test the stronger coefficientwise approach at b=1:
# h_m=x^m/(1-x+x*x)^(m+1), f_b=sum (b-1)^m h_m.
hits=[]
for m in range(1,61):
 def h(x):return x**m/(1-x+x*x)**(m+1)
 prev=(h(0),h(1))
 for n in range(2,121):
  middle=sum(h(k/n) for k in range(1,n))/n
  now=(middle,middle+1/n)
  if now[0]<prev[0]-1e-13 or now[1]>prev[1]+1e-13:
   hits.append({'m':m,'n':n,'L_diff':now[0]-prev[0],'R_diff':now[1]-prev[1]});break
  prev=now
out['coefficientwise_route_counterexamples']=hits
(P/'checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
