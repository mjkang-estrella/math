from research import *
import re
roots=[B,B.parent.parent/'2026-10-26'/'new-discoveries']
patterns={'centers':r'center[s]? of distances|centre[s]? of distances|TMNA.2023.023|2512.17285|Bartoszewicz|Filipczak|Kula', 'breadth':r'snake polynomial|Nikolov|chromatic numbers of spheres|Cherkashin|braid space|Ambrose|convex hull|cardinal functions|range of F|planar achievement|E\(p|Cantor.*sum|arithmetic sum'}
rows=[];seen=set()
for root in roots:
 for lane in (root/'lanes').glob('*'):
  if lane==L:continue
  for n in ['SUMMARY.md','SCOUTING.md','discovery.md','discovery.json']:
   p=lane/n
   if not p.is_file() or p.stat().st_size>80000:continue
   h=sha(p)
   # Immutable content reference; no scientific interpretation before digest freeze.
   q=freeze(p)
   s=q.read_text(errors='replace')
   assert sha(p)==h==sha(q)
   hits={k:re.findall(v,s,re.I)[:20] for k,v in patterns.items()}
   if any(hits.values()):rows.append({'path':str(p),'sha256':h,'hits':hits})
save('history-hits.json',rows)
print(json.dumps(rows,indent=2)[:18000])
print(fetch('https://arxiv.org/search/?query=operator+center+distances&searchtype=all','arxiv-tmna.html'))
print(fetch('https://www.bing.com/search?q=%22On+the+operator+of+center+of+distances%22+pdf','bing-tmna.html'))
