from pathlib import Path
from math import gcd
import json
L=Path(__file__).resolve().parent
ratio=json.loads((L/'next-ratio.json').read_text())[0]
from fractions import Fraction as Q
assert all(Q(s['hi'])<=Q(5,9) for s in ratio['segments'])
assert [(v['primitive']) for v in ratio['vertices'] if Q(v['x'])>Q(5,9)]==[[7,4],[8,5]]
def witness(a,t):
 A=[0]*a
 for j in range(a):A[j*t%a]=(a+1)*t if j==1 else j*t
 F=max(A)-a
 def rank(n):return sum(max(0,(n-v)//a+1) for v in A)-1
 def failed(lo,hi):
  seq=[n for n in range(max(1,lo),hi+1) if n>=A[n%a]]
  for x,y,z in zip(seq,seq[1:],seq[2:]):
   if rank(x)%3==1 and len({x%3,y%3,z%3})<3:
    assert [rank(x),rank(y),rank(z)]==list(range(rank(x),rank(x)+3))
    return [rank(x),[x,y,z]]
 s=2*t-a
 if s==1 and t%3==1:return dict(source='H2',k=(t-1)//3)
 if s==2 and t%6==5:return dict(source='H15',k=(t-5)//6)
 w=failed(1,12*a)
 if w:return dict(method='prefix',witness=w)
 assert t>=5*s and s>=3
 offsets=[0,a,2*t,3*t,2*a,a+2*t,4*t,a+3*t]
 # Independent exact gap enumeration, using membership, to certify top order.
 gaps=[n for n in range(F-a-3*t,F+1) if n<A[n%a]][::-1]
 assert gaps==[F-v for v in offsets]
 w=failed(F-4*t-3,F+3);assert w
 return dict(method='top-gaps',witness=w)
rows=[]
for t in range(7,100):
 for s in range(1,(t+1)//2):
  a=2*t-s
  if a<12 or 2*s>=t or gcd(s,t)>1:continue
  r=witness(a,t)
  # DP is independent of the Apéry construction and rank formula.
  A=[0]*a
  for j in range(a):A[j*t%a]=(a+1)*t if j==1 else j*t
  bound=max(A)+a+4;dp=[True]+[False]*bound
  for n in range(1,bound+1):dp[n]=any(n>=g and dp[n-g] for g in (a,2*t,3*t))
  assert all(v==(n>=A[n%a]) for n,v in enumerate(dp))
  seq=[n for n in range(1,bound+1) if dp[n]]
  bad=next(((i+1,seq[i:i+3]) for i in range(0,len(seq)-2,3) if len({x%3 for x in seq[i:i+3]})<3),None)
  assert (bad is None)==('source' in r)
  rows.append(dict(a=a,t=t,s=s,result=r))
targets=[dict(a=2*t-s,t=t,s=s,result=witness(2*t-s,t)) for s,t in [(4,43),(7,79),(10,109),(13,139),(3,16),(4,21),(1,7),(2,11)]]
(L/'support-checks.json').write_text(json.dumps(dict(DP_pairs=len(rows),targets=targets),indent=2)+'\n')
print('DP pairs',len(rows),'targets',targets)
