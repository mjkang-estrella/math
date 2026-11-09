from pathlib import Path
import json
L=Path(__file__).resolve().parents[2]
a=json.loads((L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json').read_text())
for f in a['families']:print(f['number'],f['title'],f['scope'])
h=json.loads((L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json').read_text())
print('Historical categories',[(k,len(v) if isinstance(v,list) else str(v)[:100]) for k,v in h.items()])
