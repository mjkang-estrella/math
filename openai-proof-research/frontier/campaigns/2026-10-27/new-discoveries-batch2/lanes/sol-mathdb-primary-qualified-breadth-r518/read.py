from pathlib import Path
import json
P=Path(__file__).resolve().parent;L=P.parent;B=L.parent
def j(p):return json.loads(p.read_text())
import sys
if '--context' in sys.argv:
 for p in [B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md',L/'root-mathdb-cayley-review-intake-r363/disposition.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'root-mathdb-breadth-intake-r517/adjudications.json',L/'root-mathdb-breadth-intake-r517/hypothesis-queue.json']:
  print(str(p),p.read_text())
else:
 rows=j(P/'assigned-records.json');a=int(sys.argv[1]);b=int(sys.argv[2])
 for d in rows[a:b]:print('\nID',d['mathdb_id'],d['record']['source_url'],'\n'+d['statement'])
