import json
from pathlib import Path
R=Path(__file__).resolve().parent
for x in json.loads((R/'records.json').read_text()):
 print(x['mathdb_id'],x['source_name'],x['source_url'],json.dumps(x['references'],ensure_ascii=False),json.dumps(x['solutions'],ensure_ascii=False))
for lane in ['root-mathdb-accepted-exclusions-r304','root-mathdb-breadth-intake-r363']:
 print('ADMIN',lane)
 p=R.parent/lane
 for n in ['README.md','DECISION.md']: 
  if (p/n).exists():print((p/n).read_text())
