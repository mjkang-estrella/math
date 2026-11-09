import json,sys
from pathlib import Path
for x in json.loads((Path(__file__).parent/'literal-records.json').read_text())[int(sys.argv[1]):int(sys.argv[2])]:
 r=x['record'];print(r['mathdb_id'],r['source_url'],'\n'+r['statement']+'\n')
