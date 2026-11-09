import json,sys
from pathlib import Path
r=json.loads((Path(__file__).parent/'literal-records.json').read_text())
for x in r[int(sys.argv[1]):int(sys.argv[2])]:
 d=x['record'];print('\n',d['mathdb_id'],d['title'],'\n',d['statement'],'\nSOURCE',d['source_url'])
