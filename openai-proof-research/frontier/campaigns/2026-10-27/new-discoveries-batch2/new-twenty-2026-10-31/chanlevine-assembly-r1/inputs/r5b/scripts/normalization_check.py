import importlib.util,json
from pathlib import Path
r=Path(__file__).resolve().parent.parent
s=importlib.util.spec_from_file_location('reviewer',r/'scripts/reviewer_brute_def.py'); a=importlib.util.module_from_spec(s);s.loader.exec_module(a)
rows=[]
for n in range(3,9):
 for m in range(1,4):
  checked=0; max_steps=0
  for x in a.compositions(n,m,0):
   for q in range(1<<n):
    recurrent=all(x[k]+x[(k+1)%n]>0 for k in range(n) if q>>k&1 and not(q>>((k+1)%n)&1))
    if not recurrent: continue
    y=list(x); b=q; steps=0
    def sink():
     global b,steps
     seen=set()
     while any(y[1:]):
      state=(tuple(y),b); assert state not in seen;seen.add(state)
      v=next(k for k in range(1,n) if y[k]);b^=1<<v;t=(v+1 if b>>v&1 else v-1)%n;y[v]-=1;y[t]+=1;steps+=1
    sink()
    if not b&1:
     assert y[0]>0;b^=1;t=1;y[0]-=1;y[t]+=1;steps+=1;sink()
    w=(sum(k*x[k] for k in range(n))+n-q.bit_count())%n
    expected=sum(1<<k for k in range(n) if not 1<=k<=w)
    assert y==[m]+[0]*(n-1) and b==expected
    checked+=1;max_steps=max(max_steps,steps)
  rows.append(dict(n=n,m=m,checked=checked,max_steps=max_steps));print(rows[-1],flush=True)
(r/'logs/normalization-check.json').write_text(json.dumps(rows,indent=2))
