from fetch import get,D
import json
print(get(('omega-root.json','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/6e37b782cf6cfe60366783f4272ac2ab8645a3e6')))
o=json.loads((D/'sources/omega-root.json').read_text())
for x in o['tree']:
 if x['path'] in ['D5','Problems']:
  print(get(('omega-'+x['path']+'.json','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+x['sha']+'?recursive=1')))
