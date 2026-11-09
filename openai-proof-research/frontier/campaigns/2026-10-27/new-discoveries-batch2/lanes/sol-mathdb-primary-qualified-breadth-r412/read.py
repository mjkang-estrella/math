import json
from pathlib import Path
for i,x in enumerate(json.loads((Path(__file__).parent/'records.json').read_text())):
 print(i,x['mathdb_id'],x['statement'],'\nSOURCE:',x['source_url'])
