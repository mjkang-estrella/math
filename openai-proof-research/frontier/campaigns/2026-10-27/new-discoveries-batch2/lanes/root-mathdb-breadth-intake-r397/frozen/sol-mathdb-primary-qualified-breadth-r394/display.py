import json
from pathlib import Path
for x in json.loads(Path(__file__).with_name('statements.json').read_text()):
 r=x['record'];print(str(r['mathdb_id'])+' '+r['title']+'\n'+r['statement']+'\nSOURCE '+r['source_url']+'\n')
