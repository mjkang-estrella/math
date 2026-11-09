from pathlib import Path
import json
for x in json.loads((Path(__file__).parent/'literal-records.json').read_text()):
 r=x['record'];print('\nID',r['mathdb_id'],'LINE',x['line']);print(r['statement']);print('SOURCE',r['source_url'],'DOCUMENTED',r.get('documented_by_source_url'))
