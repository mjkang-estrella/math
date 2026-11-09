import json
from fetch import D,get
h=json.loads((D/'sources/omega-head.json').read_text())
key='omega-root-direct.json';print(get((key,h['commit']['tree']['url'])))
p=D/'sources'/key
if p.exists():
 for x in json.loads(p.read_text())['tree']:
  if x['path'] in ['D5','Problems']:
   print(get(('omega-'+x['path']+'-tree.json',x['url']+'?recursive=1')))
