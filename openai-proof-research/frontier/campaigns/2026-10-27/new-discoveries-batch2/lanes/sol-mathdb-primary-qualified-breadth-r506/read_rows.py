from pathlib import Path
import json,sys
O=Path(__file__).parent
for j,x in enumerate(json.loads((O/'assigned-records.json').read_text())):
 if int(sys.argv[1])<=j<int(sys.argv[2]):
  r=x['record'];print(j,r['mathdb_id'],r['source_url'],'\n'+r['statement']+'\n')
