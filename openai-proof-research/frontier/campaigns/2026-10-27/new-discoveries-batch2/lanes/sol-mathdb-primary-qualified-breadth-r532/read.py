from pathlib import Path
import json
D=Path(__file__).resolve().parent;L=D.parent
for p in [L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md',D.parent.parent/'prior-campaign-context.json',D.parent.parent/'ledger.json',L/'root-mathdb-stack-park-intake-r531/adjudications.json',L/'root-mathdb-stack-park-intake-r531/hypothesis-queue.json']:
 print('\nCONTEXT',p);print(p.read_text())
for x in json.loads((D/'assigned-records.json').read_text()):
 r=x['record'];print('\nID',r['mathdb_id'],r['title'],'LINE',x['line']);print(r['statement']);print('SOURCE',r['source_name'],r['source_url'])
