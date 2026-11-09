import pathlib,json,concurrent.futures
from fetch import get
D=pathlib.Path(__file__).resolve().parents[1]
x=json.loads((D/'extracted.json').read_text()); todo=[]
for a in sorted({o['source_url'].rsplit('/',1)[-1] for o in x.values()}): todo.append((a+'-abs.html','https://arxiv.org/abs/'+a))
h=json.loads((D/'sources/omega-head.json').read_text())['sha']
todo.append(('omega-root.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{h}'))
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for v in ex.map(get,todo): print(v,flush=True)
