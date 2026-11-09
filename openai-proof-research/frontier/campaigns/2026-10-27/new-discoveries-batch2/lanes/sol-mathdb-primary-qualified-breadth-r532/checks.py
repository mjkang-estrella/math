from pathlib import Path
import json,collections
D=Path(__file__).resolve().parent;L=D.parent
G=[set() for _ in range(24)]
for v in range(24):
 for w in [(v+1)%24,(v+[12,7,-7][v%3])%24]:G[v].add(w);G[w].add(v)
assert all(len(x)==3 for x in G)
girth=100
for v in range(24):
 dist={v:0};parent={v:-1};q=collections.deque([v])
 while q:
  u=q.popleft()
  for w in G[u]:
   if w not in dist:dist[w]=dist[u]+1;parent[w]=u;q.append(w)
   elif parent[u]!=w:girth=min(girth,dist[u]+dist[w]+1)
assert girth==7
out={'construction':'cycle on Z/24 plus chord v to v+[12,7,-7][v mod 3] mod24','n':24,'m':36,'degrees':[len(x) for x in G],'girth_executed_BFS':girth,'edges':[[v,w] for v in range(24) for w in sorted(G[v]) if v<w],'necessary_fvs_lower_bound':7,'induced_forest_upper_bound':17,'conjecture_lower_bound':'132/7 = 18+6/7','mechanism':'Deleting s vertices removes at most 3s edges. If 24-s>0 vertices induce a forest, 36-3s<=24-s-1, hence s>=7. Empty remaining graph also has s>=7.','full_maximum_computation':False,'credit':0,'eligibility':'Elementary classical cycle-rank/degree count on a standard small cubic graph; no new discovery assertion; registry HOLD.'}
(D/'bounded-checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
a=json.loads((L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json').read_text())
for f in a['families']:print('FAMILY',f['number'],f.get('title'),f.get('scope'))
h=json.loads((L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json').read_text());print('HISTORICAL KEYS',h.keys());print(json.dumps(h.get('previous_excluded',[]),ensure_ascii=False))
