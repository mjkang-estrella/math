import json
from pathlib import Path
L=Path(__file__).resolve().parent
def add(a,b,shift=0,sign=1):
 c=a[:]+[0]*max(0,len(b)+shift-len(a))
 for i,v in enumerate(b):c[i+shift]+=sign*v
 return c
def prefix(a):
 s=0;out=[]
 for v in a:s+=v;out.append(s)
 return out
G=[[1]];prev={};rows=[];increment_fail=[];pair_fail=[]
for k in range(1,41):
 G=[add(G[s] if s<k else [],G[s-1] if s else [],k-s) for s in range(k+1)]
 assert all(sum(a)==__import__('math').comb(k,s) for s,a in enumerate(G))
 half=[]
 for s in range(2,k+1,2):half=add(half,G[s],s*(s+2)//2)
 for m in range(2,k//2+1):
  d=half[:]
  for s in range(2*m,k+1,2*m):d=add(d,G[s],s*(s+1)//2+s//(2*m),-1)
  p=prefix(d);assert min(p,default=0)>=0
  inc=add(d,prev.get(m,[]),sign=-1);ip=prefix(inc)
  if min(ip,default=0)<0:increment_fail.append(dict(k=k,m=m,degree=next(i for i,v in enumerate(ip) if v<0),value=min(ip)))
  rows.append(dict(k=k,m=m,degree=len(d)-1,total=sum(d),min_prefix=min(p,default=0)))
  prev[m]=d
  # Local adjacent-pair numerator after multiplying by (q;q)_k.
  s=2*m;local=add([],G[s-2],s*(s-2)//2)
  local=add(local,G[s],s*(s+2)//2)
  local=add(local,G[s],s*(s+1)//2+1,-1)
  lp=prefix(local)
  if min(lp,default=0)<0:pair_fail.append(dict(k=k,m=m,degree=next(i for i,v in enumerate(lp) if v<0),min_prefix=min(lp)))
out=dict(bounds=dict(k_max=40,exact_integer_only=True),primitive_prefix_cases=len(rows),rows=rows,increment_prefix_failures=increment_fail,local_pair_prefix_failures=pair_fail,warning='Finite diagnostics of stronger sufficient prefix criteria; failures do not refute the rational-series conjecture or a local rational-series inequality.')
(L/'checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['rows','increment_prefix_failures','local_pair_prefix_failures']}))
print('first increment prefix failure',increment_fail[:1],'first local prefix failure',pair_fail[:1])
