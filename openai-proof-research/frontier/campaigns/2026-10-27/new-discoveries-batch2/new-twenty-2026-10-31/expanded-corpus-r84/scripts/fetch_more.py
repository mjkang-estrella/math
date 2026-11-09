from fetch import get,D
import concurrent.futures,json
x=json.loads((D/'extracted.json').read_text())
a=sorted(set(o['source_url'].rsplit('/',1)[-1] for o in x.values()))
todo=[(i+'.abs.html','https://arxiv.org/abs/'+i) for i in a]+[('omega-tree.json','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/560f621894c6a54800956f8196148084589ffb51?recursive=1')]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for r in ex.map(get,todo):print(r,flush=True)
