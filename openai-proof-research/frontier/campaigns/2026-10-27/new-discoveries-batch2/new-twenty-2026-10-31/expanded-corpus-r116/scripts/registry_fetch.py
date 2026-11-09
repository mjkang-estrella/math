from fetch import get
import json
from pathlib import Path
D=Path(__file__).resolve().parents[1];s=D/'sources';o=json.loads((s/'omega-head.json').read_text());root=o['commit']['tree']['sha']
print(get(('omega-root.json','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+root)),flush=True)
r=json.loads((s/'omega-root.json').read_text())
for x in r['tree']:
 if x['path'] in ['D5','Problems']:print(get(('omega-'+x['path']+'.json','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+x['sha']+'?recursive=1')),flush=True)
