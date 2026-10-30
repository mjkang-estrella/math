"""Exact diagnostics of an already-public proof; no discovery certificate."""
import math,json,sys
from pathlib import Path
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
def ev(a,x):
 y=0
 for v in reversed(a):y=y*x+v
 return y
rows=[];old={}
for t in range(1,41):
 f=[0]*t;r=[1]
 for m in range(1,t+1):
  c=math.factorial(t)//math.factorial(m)*math.comb(t-1,m-1)
  for i,a in enumerate(r):f[i]+=c*a
  r=mul(r,[m,1])
 if t>=3:
  rhs=mul(old[t-1],[3*(t-1),1])
  for i,a in enumerate(old[t-2]):rhs[i]-=2*(t-1)*(t-2)*a
  assert rhs==f
 old[t]=f
 if t<2:continue
 root=-t-(-1)**t;M=-root
 # Binomial coefficient after the public formal-residue substitution.
 coeff=sum((-1)**j*math.comb(M,j)*math.comb(t-1,t-j) for j in range(M+1) if 0<=t-j<=t-1)
 # Direct negative-diagonal coefficient before the substitution.
 direct=sum((-2)**j*math.comb(M,j)*math.comb(M+t-j-1,t-j) for j in range(min(M,t)+1))
 assert coeff==direct==ev(f,root)==0
 rows.append(dict(t=t,root=root,polynomial_value=0,residue_coefficient=coeff,direct_coefficient=direct))
result=dict(status='PASS',scope='39 finite diagnostics of public Fayers proof, plus 38 source recurrence checks. Not a uniform proof or a fresh theorem.',rows=rows,recurrence_checks=38)
out=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('checks.json')
out.write_text(json.dumps(result,indent=2)+'\n')
print('PASS:39 negative-diagonal checks;38 recurrence checks')
