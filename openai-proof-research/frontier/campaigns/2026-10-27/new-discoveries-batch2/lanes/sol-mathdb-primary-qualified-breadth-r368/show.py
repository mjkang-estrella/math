import json,sys
from pathlib import Path
xs=json.loads(Path(__file__).with_name('records.json').read_text())
for i,x in enumerate(xs):
 if int(sys.argv[1])<=i<int(sys.argv[2]):print(i,x['mathdb_id'],x['title'],'\n'+x['statement']+'\nSOURCE '+x['source_url']+'\n')
