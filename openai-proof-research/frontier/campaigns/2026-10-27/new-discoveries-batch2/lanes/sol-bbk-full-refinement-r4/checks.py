#!/usr/bin/env python3
import os,resource,json,math
for key in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[key]='1'
resource.setrlimit(resource.RLIMIT_AS,(384*1024**2,384*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(100,100))
from pathlib import Path
N=900
# Multiply by numerator factors and divide denominator factors, without subset enumeration.
def rational(num,den,N=N):
 c=[0]*(N+1);c[0]=1
 for d in num:
  for j in range(N,d-1,-1):c[j]-=c[j-d]
 for d in den:
  for j in range(d,N+1):c[j]+=c[j-d]
 return c
def G(k,n):return rational(range(2*k-1,2*k+2*n-1,2),range(1,2*n+2,2))
def neg(c):return next(((j,x) for j,x in enumerate(c) if x<0),None)
R={'caps':{'address_space_MiB':384,'cpu_seconds':100,'degree':N,'blas_threads':1},'symmetry_pairs':0,'recurrence_pairs':0}
for k in range(2,17):
 for n in range(16):
  g=G(k,n);assert g==G(n+2,k-2);R['symmetry_pairs']+=1
  h=G(k+1,n);r=rational([2*n]+list(range(2*k+1,2*k+2*n-1,2)),list(range(1,2*n+2,2))) if n else [0]*(N+1)
  s=2*k-1
  assert [h[j]-g[j] for j in range(s,N+1)]==r[:N+1-s];assert all(h[j]==g[j] for j in range(min(s,N+1)))
  R['recurrence_pairs']+=1
  if neg(r) and 'k_monotonicity_falsifier' not in R:R['k_monotonicity_falsifier']={'k':k,'n':n,'unshifted':neg(r)}
# Canonical two-parameter cone: H(r,a) with r numerator odd factors, a odd >=2r+3.
# Stronger multiplication lemma would require (1-q^a)/(1-q^b) alone positive; false unless b|a.
R['local_multiplier_falsifier']={'num':[13],'den':[9],'negative':neg(rational([13],[9]))}
# Negative logarithmic derivative witness prevents direct Euler-exponent nonnegativity proof.
g=G(6,4); R['G6_4_prefix_min']=min(g)
R['log_derivative_witness']={'k':6,'n':4,'degree':11,'coefficient':1-11}
# Euler-transformed generating numerator at n=2: C_2=-q^5/((1+q+q^2)(1-q^5)).
g1,g2,g3=G(1,2),G(2,2),G(3,2)
c2=[g3[j]-sum(g2[j-d] for d in [0,2,4] if j>=d)+sum(g1[j-d] for d in [2,4,6] if j>=d) for j in range(N+1)]
expected=rational([1,1],[1,3,5]); expected=[0]*5+[-x for x in expected[:-5]]
assert c2==expected
R['euler_numerator_falsifier']={'n':2,'x_degree':2,'q_degree':5,'coefficient':c2[5]}
# Actual n3 even-numerator quotient, different from Chern-Wang's squared denominator.
R['short_even_quotient_falsifier']={'num':[2,4,6],'den':[1,3,5,7],'negative':neg(rational([2,4,6],[1,3,5,7]))}
# Literal k6: independent canonical/direct identity, not a positivity certificate.
assert G(6,0)==[1]*(N+1)
assert G(6,4)==rational([11,13,15,17],[1,3,5,7,9])
R['literal_k6']={'den':[1,3,5,7,9],'period':math.lcm(1,3,5,7,9),'degree':4,'G6_0_q11':G(6,0)[11],'old_smoothed_q11':rational([],[1,11])[11]}
R['process_memory_status']={line.split(':')[0]:line.split(':')[1].strip() for line in Path('/proc/self/status').read_text().splitlines() if line.startswith(('VmPeak:','VmHWM:','VmRSS:','VmSize:'))}
R['inherited_ru_maxrss_KiB']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
Path(__file__).with_name('checks.json').write_text(json.dumps(R,indent=2));print(json.dumps(R,indent=2))
