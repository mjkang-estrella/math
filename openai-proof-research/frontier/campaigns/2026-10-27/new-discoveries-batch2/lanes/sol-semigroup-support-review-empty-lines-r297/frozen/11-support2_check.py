from pathlib import Path
from math import gcd
from fractions import Fraction as Q
import json
L=Path(__file__).resolve().parent
ratio=json.loads((L/'next-ratio.json').read_text())[1]
assert all(Q(s['hi'])<=Q(5,9) for s in ratio['segments'])
assert [v['primitive'] for v in ratio['vertices'] if Q(v['x'])>Q(5,9)]==[[7,4],[8,5]]
def witness(a,t):
 A=[0]*a
 for j in range(a):A[j*t%a]=(j%3)*a+j*t
 F=max(A)-a;u=2*t-a
 def rank(n):return sum(max(0,(n-v)//a+1) for v in A)-1
 def failed(lo,hi):
  seq=[n for n in range(max(1,lo),hi+1) if n>=A[n%a]]
  for x,y,z in zip(seq,seq[1:],seq[2:]):
   if rank(x)%3==1 and len({x%3,y%3,z%3})<3:
    assert [rank(x),rank(y),rank(z)]==list(range(rank(x),rank(x)+3))
    return [rank(x),[x,y,z]]
 if u==1 and t%3==1:return dict(source='H3',k=(t-1)//3)
 if u==2 and t%6==5:return dict(source='H16',k=(t-5)//6)
 w=failed(1,12*a)
 if w:return dict(method='prefix',witness=w)
 assert u>=3 and t>=5*u and a%3==t%3!=0
 if a%3==1:
  assert F==a+(a-2)*t
  offsets=[0,a,2*a-t,a+t,3*t,2*a,3*a-t]
  endpoint=2*a
 else:
  assert F==(a-1)*t
  offsets=[0,u,a,a+u]
  endpoint=a
 gaps=[n for n in range(F-offsets[-1],F+1) if n<A[n%a]][::-1]
 assert gaps==[F-v for v in offsets],(a,t,gaps,offsets)
 w=failed(F-endpoint-3,F+3);assert w
 return dict(method='top-gaps',witness=w)
rows=[]
for t in range(7,100):
 for u in range(1,(t+1)//2):
  a=2*t-u
  if a<12 or 2*u>=t or gcd(u,t)>1:continue
  r=witness(a,t)
  A=[0]*a
  for j in range(a):A[j*t%a]=(j%3)*a+j*t
  bound=max(A)+a+4;dp=[True]+[False]*bound
  for n in range(1,bound+1):dp[n]=any(n>=g and dp[n-g] for g in (a,a+t,3*t))
  assert all(v==(n>=A[n%a]) for n,v in enumerate(dp))
  seq=[n for n in range(1,bound+1) if dp[n]]
  bad=next(((i+1,seq[i:i+3]) for i in range(0,len(seq)-2,3) if len({x%3 for x in seq[i:i+3]})<3),None)
  assert (bad is None)==('source' in r)
  rows.append(dict(a=a,t=t,u=u,result=r))
targets=[dict(a=2*t-u,t=t,u=u,result=witness(2*t-u,t)) for u,t in [(4,43),(7,79),(10,109),(13,139),(5,101),(8,191),(1,7),(2,11)]]
(L/'support2-checks.json').write_text(json.dumps(dict(DP_pairs=len(rows),targets=targets),indent=2)+'\n')
print('DP pairs',len(rows),'targets',targets)
