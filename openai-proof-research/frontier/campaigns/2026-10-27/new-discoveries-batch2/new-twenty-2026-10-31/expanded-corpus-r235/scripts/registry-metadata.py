from pathlib import Path
import sys,json
sys.path.insert(0,str(Path(__file__).resolve().parent))
from fetch import get,D
head=json.loads((D/'sources/leanpool-head.json').read_text())['sha'];tree=json.loads((D/'sources/leanpool-tree.json').read_text())
for x in tree['tree']:
 p=x['path']
 if p.startswith('candidates/') or p.endswith('projects.yml'):
  if x['type']=='blob':get('pool-'+p.replace('/','_'),'https://raw.githubusercontent.com/Vilin97/lean-pool/'+head+'/'+p)
queries=['%22Jackson%22+%22Tanigawa%22+lean','%22Cui%22+%22Hu%22+union+lean','%222212.03100%22+lean','%22Hocquard%22+lean','%22nearly+ladder%22+lean','%22Feynman%22+%22Cachazo%22+lean']
for j,q in enumerate(queries):get('github-reposearch-'+str(j)+'.json','https://api.github.com/search/repositories?q='+q)
