from pathlib import Path
import json
P=Path(__file__).resolve().parent;B=P.parent.parent;L=P.parent
for name in ['ledger.json','prior-campaign-context.json']:
 o=json.loads((B/name).read_text());print(name,'top keys',list(o));print('accepted',[(r.get('number'),r.get('title')) for r in o.get('accepted',[])])
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 o=json.loads((L/'root-mathdb-accepted-exclusions-r304'/name).read_text());print(name,'keys',list(o));
 if name=='historical-dispositions.json':print(json.dumps(o,ensure_ascii=False))
