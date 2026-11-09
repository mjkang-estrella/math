from pathlib import Path
import json
L=Path(__file__).parent
for i,r in enumerate(json.loads((L/'selected-records.json').read_text())):
 print('\n',i,r['mathdb_id'],r['title'],'\n'+r['statement']+'\nSOURCE '+str(r['source_url'])+' '+str(r.get('references')))
