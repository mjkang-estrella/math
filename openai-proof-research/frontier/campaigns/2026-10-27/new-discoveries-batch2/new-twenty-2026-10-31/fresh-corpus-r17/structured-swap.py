# Reuse independently bounded exact per-graph verifier, without rerunning its top-level sweep.
from pathlib import Path
import os,resource,time,json
P=Path(__file__).resolve().parent
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(100,100))
text=(P/'diagnostics.py').read_text();scope={};exec(text[text.index('def analyze'):text.index('rng=random')],scope);analyze=scope['analyze'];start=time.monotonic()
base=[0]*9
for h,(a,b) in enumerate([(0,1),(0,1),(1,2),(1,2),(2,0),(2,0)],3):
 for u in [a,b]:base[u]|=1<<h;base[h]|=1<<u
out={'base':analyze(base),'single_edge_repairs':[],'clique_attachments':[],'counterexamples':[]}
for i in range(9):
 for j in range(i):
  if base[i]>>j&1:continue
  a=base.copy();a[i]|=1<<j;a[j]|=1<<i;r=analyze(a);out['single_edge_repairs'].append([i,j,*r[:2]])
for size in range(1,5):
 for subset in range(1,512):
  n=9+size;a=base+[0]*size
  for i in range(9,n):
   for j in range(i):
    if j>=9 or subset>>j&1:a[i]|=1<<j;a[j]|=1<<i
  r=analyze(a);out['clique_attachments'].append([size,subset,*r[:2]])
  if r[1] and r[1]>r[0]:out['counterexamples'].append([a,r])
out['resources']={'wall_s':time.monotonic()-start,'maxrss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'cpu_limit_s':100,'as_bytes':2*1024**3,'affinity':sorted(os.sched_getaffinity(0))}
(P/'structured-swap.json').write_text(json.dumps(out,indent=2));print(len(out['clique_attachments']),out['counterexamples'],out['resources'])
