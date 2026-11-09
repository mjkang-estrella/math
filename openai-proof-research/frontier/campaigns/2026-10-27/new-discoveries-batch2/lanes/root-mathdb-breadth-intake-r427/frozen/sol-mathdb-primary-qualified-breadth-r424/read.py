import json
from pathlib import Path
p=Path(__file__).parent
for r in json.loads((p/'records.json').read_text()):
 print('\nID',r['mathdb_id'],r['title'],'\n'+r['statement']+'\nSOURCE '+str(r['source_url'])+'\nREF '+str(r['references']))
