from fractions import Fraction as F
from functools import lru_cache
import json,pathlib
L=pathlib.Path(__file__).resolve().parent
fib=[1,2]
while fib[-1]<200:fib.append(sum(fib[-2:]))
def trim(s):
 while s and s[-1]==0:s.pop()
 return tuple(s)
@lru_cache(None)
def moves(s):
 a=list(s)+[0,0];out=[]
 for i,c in enumerate(s):
  if c>=2:
   b=a.copy();b[i]-=2
   if i==0:b[1]+=1;split=0
   elif i==1:b[0]+=1;b[2]+=1;split=1
   else:b[i-2]+=1;b[i+1]+=1;split=1
   out.append((trim(b),split,'C1' if i==0 else 'S'+str(i+1)))
  if i>=1 and s[i] and s[i-1]:
   b=a.copy();b[i]-=1;b[i-1]-=1;b[i+1]+=1
   out.append((trim(b),0,'C'+str(i+1)))
 for t,_,_ in out:assert sum(x*y for x,y in zip(s,fib))==sum(x*y for x,y in zip(t,fib))
 return tuple(out)
@lru_cache(None)
def moments(s):
 m=moves(s)
 if not m:return F(0),F(0),F(0),0,1
 h=sum((moments(t)[0] for t,_,_ in m),F())/len(m)
 second=sum((moments(t)[1]+2*moments(t)[0]+1 for t,_,_ in m),F())/len(m)
 # expected accumulated predictable quadratic variation of L+h(S).
 v=sum((moments(t)[2]+(moments(t)[0]-h)**2 for t,_,_ in m),F())/len(m)
 mean=1+h;assert second-mean**2==v
 return mean,second,v,1+max(moments(t)[3] for t,_,_ in m),sum(moments(t)[4] for t,_,_ in m)
def pair(s,i,j):
 @lru_cache(None)
 def rec(s,time,early):
  m=moves(s)
  if not m:return F(early),F(0),F(0)
  if time==j:
   p=F(sum(x for _,x,_ in m),len(m));return F(early),p,early*p
  vals=[rec(t,time+1,x if time==i else early) for t,x,_ in m]
  return tuple(sum((v[k] for v in vals),F())/len(m) for k in range(3))
 return rec(s,1,0)
rows=[]
for n in range(2,19):
 s=(n,);h,q,v,d,paths=moments(s)
 best=(F(0),None)
 for i in range(2,min(d,9)):
  for j in [i+1,min(d,i+3),d]:
   if j<=i:continue
   a,b,ab=pair(s,i,j);cov=abs(ab-a*b)
   if cov>best[0]:best=(cov,[i,j])
 rows.append({'N':n,'mean':str(h),'variance':str(v),'max_length':d,'complete_move_sequences':paths,'largest_tested_single_indicator_covariance':str(best[0]),'indices':best[1]})
# Spatial empty-bin countermechanism: arbitrary width, positive left mass can fill it.
# Reverse a Fibonacci combine tree to construct one high token, then reverse the steps.
def build(k):
 if k==0:return []
 if k==1:return [('C1',1)]
 return build(k-1)+build(k-2)+[('C'+str(k),k)]
barriers=[]
for width in range(1,9):
 k=width;s=(fib[k],)+tuple([0]*k)+ (1,)
 initial=s
 for name,_ in build(k):
  options=[t for t,_,label in moves(s) if label==name];assert len(options)==1;s=options[0]
 assert s[k]==1 and s[k+1]==1
 barriers.append({'empty_width':width,'left_mass':fib[k],'initial':initial,'after_low_only_combines':s})
(L/'exact-checks.json').write_text(json.dumps({'scope':'finite exact checks only; not a CLT or uniform mixing proof','moments':rows,'states':moments.cache_info().currsize,'empty_gap_counterexamples':barriers},indent=2))
print('PASS',len(rows),'inputs;',moments.cache_info().currsize,'states; 8 empty-gap shortcut counterexamples')
