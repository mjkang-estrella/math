from pathlib import Path
import json
R=Path(__file__).resolve().parent;L=R.parent
for x in json.loads((R/'assigned-records.json').read_text()):print(x['mathdb_id'],x['source_name'],x['source_url'])
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L/'root-mathdb-breadth-intake-r437/DECISION.md',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'root-mathdb-cayley-review-intake-r363/disposition.json']:
 d=p.read_text();print('\nADMIN',p.name, d if len(d)<5000 else 'keys='+str(list(json.loads(d))))
