import json
from pathlib import Path
D=Path(__file__).resolve().parent
for x in json.loads((D/'assigned-records.json').read_text()):
 r=x['record'];print('\nID',r['mathdb_id'],r['title'],'\n'+r['statement']+'\nSOURCE '+str(r.get('source_url')))
