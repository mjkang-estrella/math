"""Re-fetch successful primary files in memory and compare retained SHA-256.

Does not overwrite retained evidence or silently accept a changed unversioned URL.
"""
import concurrent.futures, hashlib, json, urllib.request
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'frontier/sources/i08_variable_capacity_novelty_r3/literature'
items=[x for x in json.loads((OUT/'retrieval-manifest.json').read_text()) if x.get('status')=='ok']
def check(x):
    req=urllib.request.Request(x['url'],headers={'User-Agent':'Mozilla/5.0'})
    try:
        with urllib.request.urlopen(req,timeout=60) as r:b=r.read()
        actual=hashlib.sha256(b).hexdigest()
        return dict(id=x['id'],url=x['url'],matches=actual==x['sha256'],sha256=actual)
    except Exception as e:return dict(id=x['id'],url=x['url'],error=str(e),matches=False)
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:results=list(ex.map(check,items))
print(json.dumps(results,indent=2))
raise SystemExit(0 if all(x['matches'] for x in results) else 1)
