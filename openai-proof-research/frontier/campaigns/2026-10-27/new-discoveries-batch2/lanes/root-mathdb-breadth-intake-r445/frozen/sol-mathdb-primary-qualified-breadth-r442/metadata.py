from pathlib import Path
import json
R=Path(__file__).resolve().parent
for x in json.loads((R/'assigned-records.json').read_text()):
 print(x['mathdb_id'],x['source_name'],x['source_url'],json.dumps(x['references'],ensure_ascii=False), 'solutions',json.dumps(x['solutions'],ensure_ascii=False))
