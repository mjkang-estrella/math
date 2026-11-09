from pathlib import Path
import sys,json,re
sys.path.insert(0,str(Path(__file__).resolve().parent))
from fetch_sources import get,P
r=P.parent/'expanded-corpus-r254'
get(('omega-root','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+json.loads((P/'omega-head.body').read_text())['commit']['tree']['sha']))
a=json.loads((P/'omega-root.body').read_text());print([(e['path'],e['sha']) for e in a.get('tree',[])])
for e in a.get('tree',[]):
 if e['path'] in ['Blueprint','D5']:
  n='omega-current-'+e['path'];get((n,'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+e['sha']+'?recursive=1'))
  new=json.loads((P/(n+'.body')).read_text());old=json.loads((r/('omega-complete-Blueprint.body' if e['path']=='Blueprint' else 'omega-subtree-D5.body')).read_text());print(n,'truncated',new.get('truncated'),'oldtreeequal',old.get('sha')==new.get('sha'),'entries',len(new.get('tree',[])))
  before={x['path']:x['sha'] for x in old.get('tree',[])};changed=[x for x in new.get('tree',[]) if before.get(x['path'])!=x['sha']];(P/(n+'-changes.json')).write_text(json.dumps(changed,indent=2));print('CHANGED',len(changed))
print('DONE')
