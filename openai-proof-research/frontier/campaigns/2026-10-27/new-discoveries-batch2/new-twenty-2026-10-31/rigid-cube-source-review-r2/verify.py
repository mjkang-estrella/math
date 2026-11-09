import json,resource,os,collections,time
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(30,30));resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]))
b=Path(__file__).resolve().parent; a=b.parent/'expanded-corpus-r59'
c=json.loads((a/'certificate.json').read_text()); A=c['A']
# Explicit signed coordinates, repeated division, no XOR, bit_count, or author routines.
def vertex(k):
 out=[]
 for i in range(8):
  out.append(1 if k%2 else -1);k//=2
 return tuple(out)
def distance(x,y):return sum(1 for i in range(8) if x[i]!=y[i])
V=[vertex(k) for k in range(256)];S=[vertex(k) for k in A]
assert len(S)==len(set(S))==34
pairs=[distance(x,y) for x in S for y in S]; assert len(pairs)==1156 and max(pairs)==5
rows=[]
for k,x in enumerate(V):
 ds=[distance(x,y) for y in S];m=max(ds);w=A[ds.index(m)]
 assert (m==5 if k in A else m>5)
 rows.append(dict(vertex=k,member=k in A,maximum=m,witness=w))
assert sum(not r['member'] for r in rows)==222
# Validate every supplied farthest witness, independent of tie breaking.
for r in c['rows']:
 assert distance(V[r['x']],V[r['farthest_witness']])==rows[r['x']]['maximum']==r['farthest_distance']
 assert r['farthest_witness'] in A
result=dict(pass_all=True,vertices=34,ordered_pairs=len(pairs),pair_histogram=dict(collections.Counter(pairs)),rows=rows,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
(b/'diagnostics.json').write_text(json.dumps(result,indent=2))
print(json.dumps({k:v for k,v in result.items() if k!='rows'},sort_keys=True))
