import json
from pathlib import Path
W=Path(__file__).resolve().parent;L=W.parent
for f in ['accepted-exclusions.json','historical-dispositions.json']:
 o=json.loads((L/'root-mathdb-accepted-exclusions-r304'/f).read_text())
 if f.startswith('accepted'):print('\n'.join(str(x.get('number'))+' '+x.get('title','')+' '+x.get('scope','') for x in o['families']))
 else:print(json.dumps(o,ensure_ascii=False))
