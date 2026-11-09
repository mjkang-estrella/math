import runpy
from pathlib import Path
import json,re,shutil,hashlib
f=runpy.run_path(str(Path(__file__).parent/'fetch.py'))['fetch']; out=Path('prior')
# Head discovery exclusively uses /commits/HEAD. All subsequent tree access is pinned.
for repo,key,paths in [('openai/math','openai',['preprints']),('the-omega-institute/trureturing','omega',['D5','Problems'])]:
 head=json.loads((out/(key+'-head.json')).read_text())['sha']
 root=f('https://api.github.com/repos/'+repo+'/git/trees/'+head,key+'-root.json')
 if root is None: continue
 for path in paths:
  node=next((x for x in root['tree'] if x['path']==path),None)
  if node is None: print('MISSING',key,path);continue
  d=f('https://api.github.com/repos/'+repo+'/git/trees/'+node['sha']+'?recursive=1',key+'-'+path+'-tree.json')
  if d:
   matches=[x['path'] for x in d['tree'] if re.search(r'pirot|sereni|342414|edge.root|edge.pattern|chromatic.*girth|girth.*chromatic',x['path'],re.I)]
   report={'head':head,'path':path,'truncated':d.get('truncated'),'entries':len(d['tree']),'matches':matches}; (out/(key+'-'+path+'-screen.json')).write_text(json.dumps(report,indent=2)); print(report)
