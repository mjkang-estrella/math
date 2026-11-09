import pathlib,json,sys,urllib.parse
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch_receipts import get,D
s=json.loads((D/'receipts/leanpool-head/body').read_text())['sha'];t=json.loads((D/'receipts/leanpool-tree/body').read_text())
paths=[x['path'] for x in t['tree'] if x['path'].endswith(('projects.yml','projects.yaml')) or (x['path'].startswith('candidates/') and x['type']=='blob')]
print('metadata paths',len(paths))
for j,p in enumerate(paths):get('poolmeta-'+str(j),'https://raw.githubusercontent.com/Vilin97/lean-pool/'+s+'/'+p)
x=json.loads((D/'extracted.json').read_text())
for i,o in x.items():
 q=o['source_url'].rsplit('/',1)[-1]+' lean'
 get('gh-'+i,'https://api.github.com/search/repositories?q='+urllib.parse.quote(q))
