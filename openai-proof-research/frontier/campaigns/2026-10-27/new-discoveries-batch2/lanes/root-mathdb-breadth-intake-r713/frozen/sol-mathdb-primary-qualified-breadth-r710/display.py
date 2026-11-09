import json,sys
from pathlib import Path
a=json.loads((Path(__file__).parent/'literal-records.json').read_text())
for x in a[int(sys.argv[1]):int(sys.argv[2])]:
 r=x['record'];print(str(x['mathdb_id'])+' '+r['statement']+'\nSOURCE '+r['source_url']+'\n')
