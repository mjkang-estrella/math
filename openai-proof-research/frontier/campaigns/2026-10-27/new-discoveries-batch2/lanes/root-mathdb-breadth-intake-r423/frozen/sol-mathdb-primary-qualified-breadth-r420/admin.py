from pathlib import Path
import json
W=Path(__file__).resolve().parent;L=W.parent
ids=set(json.loads((L/'root-mathdb-breadth-intake-r419/reserved-ids.json').read_text())['ids'])
for name in ['root-mathdb-accepted-exclusions-r304/accepted-exclusions.json','root-mathdb-accepted-exclusions-r304/historical-dispositions.json','root-mathdb-cayley-review-intake-r363/disposition.json']:
 obj=json.loads((L/name).read_text());print(name,json.dumps(obj,ensure_ascii=False)[:14000] if 'r363' in name else 'bound; assigned numeric identifiers present: '+str([i for i in ids if str(i) in json.dumps(obj)]))
print('ledger counts',[(k,v) for k,v in json.loads((L.parent/'ledger.json').read_text()).items() if not isinstance(v,(list,dict))])
print('prior context keys',list(json.loads((L.parent/'prior-campaign-context.json').read_text())))
