from pathlib import Path
import json
D=Path(__file__).resolve().parent;L=D.parent;B=L.parent
for r in json.loads((D/'literal-records.json').read_text()):
 if 390100<=r['mathdb_id']<=390140: print(r['mathdb_id'],r['statement'])
for p in [L/'root-mathdb-breadth-intake-r579/adjudications.json',L/'root-mathdb-breadth-intake-r579/hypothesis-queue.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md']:
 print(p.name,p.read_text())
for p in [B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 a=json.loads(p.read_text()); print(p.name,'keys',list(a)[:30]);print(str(a)[:1400])
