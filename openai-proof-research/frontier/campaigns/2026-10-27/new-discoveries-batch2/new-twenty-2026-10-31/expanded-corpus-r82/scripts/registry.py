from fetch import D,get
import json
sha=json.loads((D/'sources/omega-head.json').read_text())['sha'];base='https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'
print(get(('omega-root.json',base+sha)),flush=True)
r=json.loads((D/'sources/omega-root.json').read_text())
for name in ['D5','Problems']:
 entries=[x for x in r['tree'] if x['path']==name]
 if entries:print(get(('omega-'+name+'.json',base+entries[0]['sha']+'?recursive=1')),flush=True)
