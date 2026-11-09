from pathlib import Path
import json
for x in json.loads((Path(__file__).parent/'literal-records.json').read_text()):
 r=x['record'];print(r['mathdb_id'],r['statement'], '\nSOURCE',r['source_url'],r.get('first_stated_year_source_url'),r.get('documented_by_source_url'),'\n')
