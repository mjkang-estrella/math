import pathlib,json,sys
D=pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0,str(D/'scripts'))
from fetch import get
x=json.loads((D/'reservation.json').read_text())
for key,url in [('openai-head.json','https://api.github.com/repos/openai/math/commits/HEAD'),('omega-head.json','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD')]+[(a+'.abs.html','https://arxiv.org/abs/'+a) for a in dict.fromkeys(o['source_url'].rsplit('/',1)[-1] for o in x['rows'])]:
 print(get((key,url)),flush=True)
