from pathlib import Path
import json
for v in json.loads((Path(__file__).parent/'assigned-records.json').read_text()):
 x=v['record'];print('\nID',x['mathdb_id'],x['title'],'SOURCE',x['source_url']);print(x['statement'])
