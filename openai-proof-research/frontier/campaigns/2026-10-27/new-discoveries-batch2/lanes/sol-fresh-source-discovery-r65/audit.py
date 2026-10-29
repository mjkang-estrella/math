import json,hashlib,re
from pathlib import Path
P=Path(__file__).resolve().parent;B=P.parent.parent
terms=re.compile(r'latin.?euler|mirzavaziri|yaqubi|converse.?invariant|crown.?poset|glasby',re.I)
rows=[]
for f in [B/'ledger.json',B/'prior-campaign-context.json',B/'NEXT.md']+list(B.glob('lanes/*/SUMMARY.md')):
 data=f.read_bytes();s=data.decode(errors='replace')
 rows.append(dict(file=str(f.relative_to(B)),sha256=hashlib.sha256(data).hexdigest(),hits=[x[:700] for x in s.splitlines() if terms.search(x)]))
# Reuse saved registry trees; lexical screening is only triage, never full-body clearance.
for lane in ['sol-fresh-source-discovery-r61','root-polyomino57-acceptance-r1']:
 for f in (B/'lanes'/lane).rglob('*.json'):
  if f.stat().st_size>15000000:continue
  data=f.read_bytes();s=data.decode(errors='replace')
  if 'tree' not in s or not terms.search(s):continue
  try:j=json.loads(s)
  except ValueError:continue
  entries=j.get('tree',[]) if isinstance(j,dict) else []
  hits=[x.get('path') for x in entries if isinstance(x,dict) and terms.search(x.get('path',''))]
  rows.append(dict(file=str(f.relative_to(B)),sha256=hashlib.sha256(data).hexdigest(),hits=hits,limit='lexical cached paths only'))
(P/'context-screen.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps([x for x in rows if x['hits']],indent=2))
