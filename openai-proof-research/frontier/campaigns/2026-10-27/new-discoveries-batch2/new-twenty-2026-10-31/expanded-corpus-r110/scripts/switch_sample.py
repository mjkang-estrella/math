exec(open(__file__.replace('switch_sample.py','switch2.py')).read().split('for L in range(1,11):')[0])
import random
rng=random.Random(110)
for L in [12,16,24,32,64,100]:
 tested=bad=0;rows={}
 for it in range(10000):
  b=it%4;a=L-b;w=tuple(rng.randrange(3) for _ in range(L));n=2*a+b
  if n%3==0:continue
  v=make(w,a,b)
  if v is None:continue
  u=make(tuple(reversed(w)),b,a,False);tested+=1;rows[n]=rows.get(n,0)+1
  if v!=u:bad+=1;print(json.dumps(dict(failure=dict(L=L,a=a,b=b,w=w,v=v,u=u))),flush=True)
 print(json.dumps(dict(objects=L,placement_samples=10000,valid_inputs=tested,by_rows=rows,mismatches=bad)),flush=True)
