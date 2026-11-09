from fetch import get,D
import json,concurrent.futures
x=json.load(open(D/'extracted.json'));todo=[]
for a in sorted(set(o['source_url'].split('/')[-1] for o in x.values())):todo.append((a+'.abs.html','https://arxiv.org/abs/'+a))
omega=json.load(open(D/'sources/omega-head.json'))['sha']
todo.append(('omega-tree.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{omega}'))
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for r in ex.map(get,todo):print(r,flush=True)
