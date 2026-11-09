# Fetch Omega root tree at current HEAD, then the complete Problems subtree; search for reserved IDs, source arXiv numbers and author/title keywords.
import json,pathlib,sys
sys.path.insert(0,str(pathlib.Path(__file__).parent))
from fetch import get
D=pathlib.Path(__file__).resolve().parents[1]
h=json.loads((D/'sources/omega-head.json').read_text()); tree=h['commit']['tree']['sha']; print('omega',h['sha'],tree,flush=True)
get(('omega-root-tree.json',f"https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{tree}"))
root=json.loads((D/'sources/omega-root-tree.json').read_text())
for name in ['Problems','D5']:
 sha=[x['sha'] for x in root['tree'] if x['path']==name][0]
 get((f'omega-{name}-tree.json',f"https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{sha}?recursive=1"))
 t=json.loads((D/f'sources/omega-{name}-tree.json').read_text()); print(name,sha,'truncated',t.get('truncated'),'entries',len(t.get('tree',[])),flush=True)
