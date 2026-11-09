from pathlib import Path
import json,sys,time,urllib.parse
sys.path.insert(0,str(Path(__file__).resolve().parent));from fetch import get,D
sha=json.loads((D/'sources/pool-head.json').read_text())['sha'];print('POOL',sha)
get('pool-tree.json',f'https://api.github.com/repos/Vilin97/lean-pool/git/trees/{sha}?recursive=1')
t=json.loads((D/'sources/pool-tree.json').read_text())
for x in t['tree']:
 p=x['path']
 if p=='projects.yml' or (p.startswith('candidates/') and x['type']=='blob'):
  get('pool-'+p.replace('/','__'),f'https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/{p}')
