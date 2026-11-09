import pathlib,json,sys
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch import get
D=pathlib.Path(__file__).resolve().parents[1]
for k,vs in json.loads((D/'outputs/versions.json').read_text()).items():
 a=k.split('-abs')[0]
 for v in vs:
  key=a+'v'+v+'.html'
  if not (D/'sources'/key).exists():get(key,'https://arxiv.org/html/'+a+'v'+v)
get('1808.01008.pdf','https://arxiv.org/pdf/1808.01008')
get('polycyclic-followup-abs.html','https://arxiv.org/search/?query=Equivalence+and+duality+of+polycyclic+codes&searchtype=title')
