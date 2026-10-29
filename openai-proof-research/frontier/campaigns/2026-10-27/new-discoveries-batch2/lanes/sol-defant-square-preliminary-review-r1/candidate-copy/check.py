import os,resource,signal,json,bisect
from fractions import Fraction as Q
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(25,25));signal.alarm(35)
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
b=Path(__file__).resolve().parent
N=600000
s=bytearray(b'\1')*(N+1);s[:2]=b'\0\0'
for i in range(2,776):
 if s[i]:s[i*i::i]=b'\0'*((N-i*i)//i+1)
ps=[i for i in range(N+1) if s[i]]
small=[];checks=0;ids=0
for r in range(1,201):
 a=ps[bisect.bisect(ps,r)]
 assert r<a<=2*r
 for p in ps:
  if p>997:break
  if p<=r:continue
  x=Q(p*p,a);q=ps[bisect.bisect(ps,x)]
  m=a*q;lhs=(a-r)*(q-r);rhs=p*(p-r)
  assert q>p and m>p*p and 0<lhs<=rhs
  if x>=11:assert q<=Q(7,5)*x<Q(3,2)*x
  elif (r,p,a,q,m,lhs,rhs) not in small:small.append((r,p,a,q,m,lhs,rhs))
  A=Q(3*r-a,2*a)
  F=p*(p-r)-(a-r)*(Q(3,2)*Q(p*p,a)-r)
  rhsF=A*(p-a)**2+(2*r-a)*(p-a)+(a-r)*(r-Q(a,2))
  assert F==rhsF and F>=0
  checks+=1;ids+=1
assert len(small)==10
# Exactly the finite prime-gap base in Defant's lemma, independently reproduced.
gaps=0
for u,v in zip(ps,ps[1:]):
 if u>396738:break
 if u not in [2,3,7]:assert 5*v<=7*u;gaps+=1
out={'status':'PASS','witness_pairs_r_le_200_p_le_997':checks,'exact_identity_checks':ids,'prime_gap_base_checks':gaps,'small_cases_columns':['r','p','a','q','m','S_r(m)','S_r(p^2)'],'small_cases':small,'scope':'Finite checks supplement the ordinary proof; not its all-order argument. No randomness.'}
(b/'check-output.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
