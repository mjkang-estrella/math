import sys,json,urllib.parse,time
import pathlib;sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch import D,fetch
repo='Vilin97/lean-pool';sha=json.loads((D/'sources/Vilin97-lean-pool-head.json').read_text())['sha'];tree=json.loads((D/'sources/Vilin97-lean-pool-tree.json').read_text())['tree']
paths=[x['path'] for x in tree if x['type']=='blob' and (x['path']=='LeanPool/projects.yml' or x['path'].startswith('candidates/'))]
for p in paths:fetch('https://raw.githubusercontent.com/'+repo+'/'+sha+'/'+p,'pool-'+p.replace('/','-'))
