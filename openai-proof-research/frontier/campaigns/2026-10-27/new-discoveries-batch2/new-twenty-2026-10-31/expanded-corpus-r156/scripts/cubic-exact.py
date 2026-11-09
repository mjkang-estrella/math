import sys,time,json,pathlib,itertools,runpy
# Load definitions without running the random sweep.
src=pathlib.Path('scripts/cycles.py').read_text();scope={};exec(src[:src.index('for n in [8,10')],scope);check=scope['check']
n=int(sys.argv[1]);start=time.monotonic();A=[set() for _ in range(n)];count=0;cyclecount=0;nodes=0;complete=True
for j in [1,2,3]:A[0].add(j);A[j].add(0)
def save(done):
 o={'n':n,'first_vertex_neighbours_fixed':[1,2,3],'graphs_tested':count,'total_5cycles':cyclecount,'nodes':nodes,'complete':done,'seconds':time.monotonic()-start,'counterexample':None,'scope':'All simple triangle-free labelled cubic graphs with N(0)={1,2,3}; label fixing loses no isomorphism type. Connectedness not required.'}
 pathlib.Path(f'outputs/cubic-exact-{n}.json').write_text(json.dumps(o,indent=2));print(json.dumps(o),flush=True)
def rec(v):
 global count,cyclecount,nodes
 nodes+=1
 if nodes%4096==0 and time.monotonic()-start>110:raise TimeoutError
 while v<n and len(A[v])==3:v+=1
 if v==n:
  E={(a,b) for a in range(n) for b in A[a] if a<b};ok,c=check(n,E);count+=1;cyclecount+=c
  if not ok:pathlib.Path('outputs/cubic-counterexample.json').write_text(json.dumps({'n':n,'edges':sorted(E)}));raise ValueError('counterexample')
  return
 need=3-len(A[v]);cands=[b for b in range(v+1,n) if len(A[b])<3 and b not in A[v] and not A[v]&A[b]]
 for B in itertools.combinations(cands,need):
  if any(b in A[c] for b,c in itertools.combinations(B,2)):continue
  for b in B:A[v].add(b);A[b].add(v)
  rec(v+1)
  for b in B:A[v].remove(b);A[b].remove(v)
try:rec(1)
except TimeoutError:complete=False
save(complete)
