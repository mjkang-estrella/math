from pathlib import Path
from itertools import combinations
import json, hashlib
R=Path(__file__).resolve().parent
B=R.parent
v=[2,5,2,0,4,3,5,0,1,6,4,6]
e=[0,1,4,5,1,2,6,4,3,5,2,4]
g=[(i,(i+1)%12) for i in range(12)]
h=[x for i,x in enumerate(g) if i%3!=2]
def check(edges,vc,ec):
 adj=[{b if a==i else a for a,b in edges if i in (a,b)} for i in range(12)]
 inc=[{ec[j] for j,x in enumerate(edges) if i in x} for i in range(12)]
 p={x:[] for x in ['E','V','T','N']}
 for i in range(12):
  w={vc[j] for j in adj[i]|{i}}
  for k,x in [('E',inc[i]),('V',w),('T',inc[i]|{vc[i]}),('N',inc[i]|w)]:p[k].append(sorted(x))
 proper=(all(vc[a]!=vc[b] and ec[j] not in (vc[a],vc[b]) for j,(a,b) in enumerate(edges)) and all(ec[j]!=ec[k] for j,k in combinations(range(len(edges)),2) if set(edges[j])&set(edges[k])))
 injective={k:len({tuple(s) for s in val})==12 for k,val in p.items()}
 return {'proper_total':proper,'palettes':p,'all_pairs_injective':injective,'all_eight':proper and all(injective.values()),'degrees':[len(x) for x in adj],'distinct_closed_neighborhoods':len({tuple(sorted(x|{i})) for i,x in enumerate(adj)})==12,'no_isolated_edges':all(not(len(adj[a])==len(adj[b])==1) for a,b in edges)}
a=check(g,v,e);b=check(h,list(range(12)),list(range(12,20)))
assert a['all_eight'] and b['all_eight']
# Independently parse each published palette row and compare to recomputation.
rows={}
for line in (B/'fresh-corpus-r12/MATHEMATICS.md').read_text().splitlines():
 if line.startswith('|'):
  cols=line.strip('|').split('|')
  if len(cols)==5 and cols[0].isdigit():rows[int(cols[0])]=[list(map(int,x)) for x in cols[1:]]
assert len(rows)==12
assert all(rows[i]==[a['palettes'][k][i] for k in ['E','V','T','N']] for i in range(12))
leaves=[i for i,d in enumerate(b['degrees']) if d==1]
leafedges=[next(j for j,x in enumerate(h) if i in x) for i in leaves]
assert len(leaves)==len(set(leafedges))==8
p=json.loads((B/'fresh-corpus-r12/results.json').read_text())['332204']['provenance']
f=Path(p['chunk']); raw=f.read_bytes();line=raw.splitlines(keepends=True)[p['line']-1]
# Bind the original complete JSONL line bytes, including its terminator.
linehash=hashlib.sha256(line).hexdigest()
assert hashlib.sha256(raw).hexdigest()==p['chunk_sha256']
assert linehash==p['line_sha256']
result={'G':a,'H_unique_20_coloring':b,'palette_table_matches':True,'leaves':leaves,'leaf_edge_indices_in_H':leafedges,'leaf_bound':8,'G_upper':7,'H_upper':20,'same_vertex_set':True,'deleted_edge_indices':[2,5,8,11],'proper_spanning_subgraph':True,'provenance':p,'provenance_chunk_and_line_hashes_match':True,'scope':'exact finite checks plus ordinary pigeonhole proof in REVIEW.md; not Lean'}
(R/'independent-check.json').write_text(json.dumps(result,indent=2))
print('PASS: proper7 coloring; all four palette injections; table; H20 finiteness; eight distinct leaf edges; exact corpus provenance')
