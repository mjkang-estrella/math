from pathlib import Path
import json
W=Path(__file__).resolve().parent
for r in json.loads((W/'records.json').read_text()):print(str(r['mathdb_id'])+' '+r['statement']+'\nSOURCE '+r['source_url']+'\n')
