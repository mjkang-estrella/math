import json,sys
from pathlib import Path
r=json.loads((Path(__file__).parent/'literal-records.json').read_text())
for x in r[int(sys.argv[1]):int(sys.argv[2])]:
 s=x['record'];print('\nID',x['id'],s['title'],'\nSOURCE',s['source_url'],'\n',s['statement'])
