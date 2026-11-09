from pathlib import Path
import json
R=Path(__file__).parent
for x in json.loads((R/'selected-records.json').read_text()):
 print(x['mathdb_id'],x['title'],'SOURCE',x['source_name'],x['source_url'],'REF',x['references'],'SOL',x['solutions'])
