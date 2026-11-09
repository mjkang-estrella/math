import random,json
from pathlib import Path
random.seed(332204)
n=12;k=7
for it in range(300000):
 v=[random.randrange(k) for _ in range(n)]; e=[random.randrange(k) for _ in range(n)]
 if any(v[i]==v[(i+1)%n] or e[i] in [v[i],v[(i+1)%n],e[(i+1)%n]] for i in range(n)):continue
 palettes=[[frozenset([e[i-1],e[i]]) for i in range(n)], [frozenset([v[i-1],v[i],v[(i+1)%n]]) for i in range(n)], [frozenset([e[i-1],e[i],v[i]]) for i in range(n)], [frozenset([e[i-1],e[i],v[i-1],v[i],v[(i+1)%n]]) for i in range(n)]]
 if all(len(set(p))==n for p in palettes):
  row={'n':n,'k':k,'vertex_colors':v,'edge_colors':e,'palettes':[[sorted(s) for s in p] for p in palettes],'iterations':it};print(row);Path(__file__).with_name('coloring-diagnostics.json').write_text(json.dumps(row,indent=2));break
else: print('No witness by naive independent sampling; no infeasibility conclusion.')
