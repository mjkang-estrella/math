from pathlib import Path
import json
L=Path(__file__).resolve().parent
h=json.loads((L/'http/leanpool-head.json').read_text())['sha']
jobs=[['leanpool-tree.json',f'https://api.github.com/repos/Vilin97/lean-pool/git/trees/{h}?recursive=1']]
tree=json.loads((L.parent/'expanded-corpus-r250/sources/leanpool-tree.json').read_text())
for x in tree['tree']:
 p=x['path']
 if p.startswith('candidates/') and x['type']=='blob' and '/' not in p[len('candidates/'):]: jobs.append(['pool-'+p.replace('/','--'),f'https://raw.githubusercontent.com/Vilin97/lean-pool/{h}/{p}'])
(L/'registry-jobs.json').write_text(json.dumps(jobs));print(h,len(jobs))
