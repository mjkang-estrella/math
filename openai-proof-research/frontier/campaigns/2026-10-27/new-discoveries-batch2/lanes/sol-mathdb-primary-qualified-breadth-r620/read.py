from pathlib import Path
import json
P=Path(__file__).resolve().parent;L=P.parent;B=L.parent
for n in ['root-mathdb-breadth-intake-r619/adjudications.json','root-mathdb-breadth-intake-r619/hypothesis-queue.json','root-mathdb-cayley-review-intake-r363/DECISION.md','root-mathdb-accepted-exclusions-r304/accepted-exclusions.json','root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 print(n,(L/n).read_text()[:16000])
for n in ['ledger.json','prior-campaign-context.json']:print(n,(B/n).read_text()[:5000])
rs=json.loads((P/'literal-records.json').read_text())
for x in rs:
 r=x['record'];print('\nID',r['mathdb_id'],json.dumps(r,ensure_ascii=False))
