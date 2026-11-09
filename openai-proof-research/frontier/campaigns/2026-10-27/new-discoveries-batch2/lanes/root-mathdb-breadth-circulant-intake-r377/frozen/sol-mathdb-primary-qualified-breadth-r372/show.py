from pathlib import Path
import json,sys
rs=json.loads((Path(__file__).parent/'records.json').read_text())
for r in rs[int(sys.argv[1]):int(sys.argv[2])]: print(str(r['mathdb_id'])+' '+r['title']+'\n'+r['statement']+'\n'+r['source_url']+'\n')
