import pathlib,json,re,sys
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch_receipts import get,D,DENIED
DENIED.update(['api.github.com','www.mdpi.com'])
x=json.loads((D/'extracted.json').read_text())
for i,o in x.items():
 vs=re.findall(r'\[v(\d+)\]',(D/'sources'/f'{i}-abs.txt').read_text())
 if len(vs)>1:
  for v in vs:get(i+'-version'+v,'https://arxiv.org/html/'+o['source_url'].rsplit('/',1)[-1]+'v'+v)
get('omega-amoeba','https://raw.githubusercontent.com/the-omega-institute/trureturing/main/Problems/gurvich-krnc-vyalyi-conjecture-1-total-amoeba-confinement.md')
