import json,sys,itertools
from pathlib import Path
D=Path(__file__).resolve().parents[1];a=int(sys.argv[1]);cube=list(itertools.product(range(2),repeat=3));ci={x:i for i,x in enumerate(cube)};cl=[[ci[tuple(v-1 if t==k else v for t,v in enumerate(x))] for k in range(3) if x[k]] for x in cube];heights=[];states=set()
def gen(i):
 if i==8:
  # heights monotone on (j,k,t); convert by reversing j,k to nested threshold counts
  f=tuple(sum(v>=heights[ci[(1-j,1-k,t)]] for t in range(2)) for v in range(a) for j in range(2) for k in range(2));states.add(f);return
 for v in range(max([heights[j] for j in cl[i]]+[0]),a+1):heights.append(v);gen(i+1);heights.pop()
gen(0);total=len(states);print('a',a,'states',total,flush=True)
pts=list(itertools.product(range(a),range(2),range(2)));idx={x:i for i,x in enumerate(pts)};low=[];up=[]
for x in pts:
 low.append([idx[tuple(v-1 if t==k else v for t,v in enumerate(x))] for k in range(3) if x[k]])
 up.append([idx[tuple(v+1 if t==k else v for t,v in enumerate(x))] for k in range(3) if x[k]+1<(a,2,2)[k]])
order=sorted(range(4*a),key=lambda i:sum(pts[i]),reverse=True);orbits=0;maxperiod=0;violations=[]
while states:
 start=states.pop();f=list(start);sums=list(f);period=1
 while True:
  for j in order:f[j]=max([f[i] for i in low[j]]+[0])+min([f[i] for i in up[j]]+[2])-f[j]
  if tuple(f)==start:break
  assert tuple(f) in states
  states.remove(tuple(f));sums=[s+v for s,v in zip(sums,f)];period+=1
 orbits+=1;maxperiod=max(maxperiod,period)
 if any(sums[j]+sums[4*a-1-j]!=2*period for j in range(4*a)):violations.append([start,period,sums]);break
out=dict(a=a,total_states=total,orbits=orbits,maxperiod=maxperiod,violations=violations,unprocessed=len(states));print(json.dumps(out),flush=True);(D/f'outputs/promotion-exhaust-{a}.json').write_text(json.dumps(out,indent=2)+'\n')
