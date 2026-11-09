from fetch import get,D
import json,concurrent.futures
x=json.loads((D/'extracted.json').read_text());todo=[]
for o in x.values():
 if 'arxiv' in o['source_url']:todo.append((o['source_url'].rsplit('/',1)[-1]+'.abs.html',o['source_url']))
for name,repo in [('omega','the-omega-institute/trureturing'),('openai','openai/math')]:
 h=json.loads((D/'sources'/f'{name}-head.json').read_text())['sha'];todo.append((name+'-tree.json',f'https://api.github.com/repos/{repo}/git/trees/{h}?recursive=1'))
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for r in ex.map(get,todo):print(r,flush=True)
