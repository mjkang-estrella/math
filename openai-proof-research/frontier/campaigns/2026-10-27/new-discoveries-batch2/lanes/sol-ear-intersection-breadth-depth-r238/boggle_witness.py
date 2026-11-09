from pathlib import Path
from itertools import permutations
import json
L=Path(__file__).resolve().parent
r=json.loads((L/'breadth-checks.json').read_text())['boggle'];s=r['valid_eleven_clues'][0];E=[e for i,e in enumerate(r['grid_edges']) if s>>i&1]
def adj(a,b):return a!=b and max(abs(a//3-b//3),abs(a%3-b%3))==1
sol=[p for p in permutations(range(9)) if all(adj(p[a],p[b]) for a,b in E)]
assert len(sol)==8
# Standard source labels, clockwise boundary 1..8 and center9.
labels=[1,2,3,8,9,4,7,6,5]
out=dict(clues_zero_based=E,clues_source_labels=[[labels[a],labels[b]] for a,b in E],embeddings=sol,degrees={i:sum(i in e for e in E) for i in range(9)},status='exact finite candidate; ordinary human proof and current prior-art clearance pending')
out['all_twelve_support_sizes']=[len({v for i,e in enumerate(r['grid_edges']) if m>>i&1 for v in e}) for m in r['valid_eleven_clues']]
(L/'boggle-witness.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
