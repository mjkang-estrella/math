from fetch import get,D
import json
h=json.loads((D/'sources/omega-head.json').read_text())['sha']
get(('omega-root.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{h}'))
o=json.loads((D/'sources/omega-root.json').read_text())
for t in o.get('tree',[]):
 if t['path'] in ['D5','Problems']:get(('omega-'+t['path']+'.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{t["sha"]}?recursive=1'))
# Immutable older source needed: current source no longer contains the literal diameter conjecture.
get(('2510.23022v1.html','https://arxiv.org/html/2510.23022v1'))
get(('2509.02841.pdf','https://arxiv.org/pdf/2509.02841'))
