from fetch import D,get
import json
for i,o in json.loads((D/'extracted.json').read_text()).items():
 if 'wikipedia.org' in o['source_url']:print(get((i+'-reference.html',o['source_url'])),flush=True)
