import json
from fetch import D,get
for item in [('omega-root.json','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/4bd2c7bde1033460640db2b117cfa3d2be6de5e0'),('harmonic-followup.html','https://arxiv.org/html/2606.15761v3')]:print(get(item))
d=json.loads((D/'sources/omega-root.json').read_text())
for x in d['tree']:
 if x['path'] in ['D5','Problems']:
  print(get(('omega-'+x['path']+'-tree.json',x['url']+'?recursive=1')))
