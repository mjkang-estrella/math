import pathlib,sys,json,re
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch_receipts import get,D,DENIED
DENIED.update(['api.github.com','www.mdpi.com'])
s=json.loads((D/'receipts/leanpool-head/body').read_text())['sha']
# Immutable raw host differs from denied API host; no redirection into API permitted.
get('openai-overview','https://raw.githubusercontent.com/openai/math/main/overview.tex')
get('leanpool-projects-correct','https://raw.githubusercontent.com/Vilin97/lean-pool/'+s+'/LeanPool/projects.yml')
p=D.parent/'expanded-corpus-r174/sources/omega-Problems-tree.json'
x=json.loads(p.read_text());paths=[o['path'] for o in x.get('tree',[]) if re.search('gurvich|krnc|amoeba',o['path'],re.I)];(D/'outputs/omega-cached-paths.json').write_text(json.dumps({'input':str(p),'paths':paths},indent=2))
get('omega-readme','https://raw.githubusercontent.com/the-omega-institute/trureturing/main/README.md')
get('starforests2025','https://arxiv.org/html/2509.18567')
get('dominion2024-doi','https://doi.org/10.3390/math12213408')
