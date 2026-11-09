"""Exact finite impartial-game diagnostic for the primary clause only."""
from functools import cache
import json
from pathlib import Path
G=[frozenset()]; idx={G[0]:0}
def game(opts):
 f=frozenset(opts)
 if f not in idx:idx[f]=len(G);G.append(f)
 return idx[f]
star=game([0])
@cache
def adj(a):return star if not G[a] else game(adj(x) for x in G[a])
@cache
def p(a,b):
 opts=[(x,b) for x in G[a]]+[(a,y) for y in G[b]]
 return bool(opts) and not any(p(x,y) for x,y in opts)
if __name__=='__main__':
 # all options subsets of the first 8 hereditary-finite games
 for mask in range(256):game(i for i in range(8) if mask>>i&1)
 n=len(G); A=[adj(i) for i in range(n)]
 rel=[[p(b,A[a]) for b in range(n)] for a in range(n)]
 out={'tested_games':n,'relation':'P(b + adj(a))','counterexample':None}
 for a in range(n):
  for b in range(n):
   if rel[a][b]:
    for c in range(n):
     if rel[b][c] and not rel[a][c]:out['counterexample']=[a,b,c];break
   if out['counterexample']:break
  if out['counterexample']:break
 out['option_sets']={str(i):sorted(G[i]) for i in range(n)}
 Path(__file__).with_name('misere-diagnostic.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items() if k!='option_sets'})
