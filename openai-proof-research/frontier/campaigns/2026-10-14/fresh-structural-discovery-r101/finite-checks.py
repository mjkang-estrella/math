"""Read-only exact support checks; not a full-game proof or independent review."""
import json,itertools,subprocess,sys
from pathlib import Path
from collections import Counter
r=Path(__file__).absolute().parent
S={(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)}
def orient(k):return {((-1 if k&1 else 1)*(y if k&4 else x),(-1 if k&2 else 1)*(x if k&4 else y)) for x,y in S}
C=Counter()
for k in range(8):
 for a,b in itertools.combinations(orient(k),2):
  d=(b[0]-a[0],b[1]-a[1]);C[min(d,(-d[0],-d[1]))]+=1
assert max(C.values())==20 and 8*100**2*3>20*108**2
p=json.loads((r/'square-eight-packing.json').read_text());A=set(map(tuple,p['initial']));es=[set(map(tuple,e)) for e in p['disjoint_residual_triples']];H=set(map(tuple,p['eight_cell_transversal']))
assert len(es)==len(H)==8 and all(len(e)==3 and not A&e for e in es)
assert len(set().union(*es))==24
T=set()
for k in range(8):
 sh=orient(k)
 for a in A:
  for x,y in sh:
   B=frozenset((u+a[0]-x,v+a[1]-y) for u,v in sh)
   if len(B-A)<=4:T.add(B)
assert len(T)==64 and all((B-A)&H for B in T)
assert all(any(B-A==e for B in T) for e in es)
for stem in ['two-turn-screen','four-stone-screen']:
 q=subprocess.run([sys.executable,str(r/(stem+'.py'))],check=True,capture_output=True,text=True)
 assert json.loads(q.stdout)==json.loads((r/(stem+'.json')).read_text())
print(json.dumps({'status':'PASS','canonical_initial_triples':11,'four_stone_configurations':136,'square_disjoint_triples':8,'square_targets_hit':64,'edge_displacement_classes':len(C),'degree2_incidence_contradiction':[240000,233280],'limits':'Exact finite support checks only; no full threshold, no UNSAT certification, no independent review.'}))
