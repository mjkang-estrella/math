from pathlib import Path
import json,re
L=Path(__file__).resolve().parent;D=L/'http';j=[]
t=json.loads((D/'omega-root.json').read_text())
for x in t['tree']:
 if x['type']=='tree' and x['path'] in ['D5','Problems','Reg']:j.append(['omega-'+x['path']+'-tree.json',x['url']+'?recursive=1'])
# Read registry candidate indexes in their actual location.
t=json.loads((D/'pool-tree.json').read_text())
for x in t['tree']:
 p=x['path']
 if x['type']=='blob' and 'candidates/' in p and p.count('/')<=2:
  j.append(['pool-candidate-'+p.replace('/','--'),'https://raw.githubusercontent.com/Vilin97/lean-pool/01db1d7049cf9668bda1e9e106875ee1278b43e6/'+p])
(L/'registry-more-plan.json').write_text(json.dumps(j));print('jobs',len(j))
