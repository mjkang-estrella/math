from pathlib import Path
import random,json,sys
D=Path(__file__).resolve().parents[1];rng=random.Random(980354562);out=[]
# Piecewise-linear rowmotion on A^2([a]x[2]x[2]); source Cor 3.4 and Phi translate this to Conj 3.36.
for a in [1,2,3,4,5,6,7,8,9,10,12,16,24,32]:
 pts=[(i,j,k) for i in range(a) for j in range(2) for k in range(2)];idx={x:i for i,x in enumerate(pts)}
 low=[];up=[]
 for x in pts:
  low.append([idx[tuple(y-1 if t==c else y for t,y in enumerate(x))] for c in range(3) if x[c]>0])
  up.append([idx[tuple(y+1 if t==c else y for t,y in enumerate(x))] for c in range(3) if x[c]+1<(a,2,2)[c]])
 order=sorted(range(len(pts)),key=lambda j:sum(pts[j]),reverse=True);tests=0;maxorb=0;bad=[];truncated=0
 for trial in range(80):
  # Generate order-preserving random 0..2 labelings by max of lower covers.
  f=[]
  for t,x in enumerate(pts):f.append(rng.randint(max([f[i] for i in low[t]]+[0]),2))
  start=tuple(f);sums=[0]*len(f);period=0
  while True:
   for j,v in enumerate(f):sums[j]+=v
   for j in order:f[j]=max([f[i] for i in low[j]]+[0])+min([f[i] for i in up[j]]+[2])-f[j]
   period+=1
   if tuple(f)==start:break
   if period==10000:break
  if tuple(f)!=start:truncated+=1;continue
  tests+=1;maxorb=max(maxorb,period)
  for j,x in enumerate(pts):
   anti=idx[(a-1-x[0],1-x[1],1-x[2])]
   if sums[j]+sums[anti]!=2*period:bad.append([trial,j,period,sums[j]+sums[anti]])
 row=dict(a=a,completed_orbits=tests,max_period=maxorb,truncated=truncated,violations=bad);out.append(row);print(json.dumps(row),flush=True)
(D/'outputs/promotion.json').write_text(json.dumps(out,indent=2)+'\n')
