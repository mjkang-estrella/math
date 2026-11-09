from fetch import get,D
import json,concurrent.futures
x=json.loads((D/'extracted.json').read_text());urls=sorted(set(o['source_url'] for o in x.values()))
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for r in ex.map(get,[(u.rsplit('/',1)[-1]+'.abs.html',u) for u in urls]):print(r,flush=True)
