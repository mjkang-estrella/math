from pathlib import Path
import json,sys
O=Path(__file__).resolve().parent
for i,a in enumerate(json.loads((O/'assigned-records.json').read_text())):
 if int(sys.argv[1])<=i<int(sys.argv[2]):
  r=a['record'];print('\n',i+1,r['mathdb_id'],r['source_url'],'\n'+r['statement'])
