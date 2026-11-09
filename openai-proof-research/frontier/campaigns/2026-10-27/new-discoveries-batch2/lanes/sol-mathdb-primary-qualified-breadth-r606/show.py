from pathlib import Path
import json,sys
r=json.loads((Path(__file__).parent/'literal-records.json').read_text())
for x in r[int(sys.argv[1]):int(sys.argv[2])]:
 a=x['record'];print(a['mathdb_id'],a['title'],'\n',a['statement'],'\nSOURCE',a['source_url'],'\n')
