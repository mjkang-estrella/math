from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import requests,json,hashlib,datetime
p=Path(__file__).resolve().parent/'sources'
urls={'source-v1.pdf':'https://arxiv.org/pdf/2510.03600v1','source-v1.html':'https://arxiv.org/html/2510.03600v1','source-abs.html':'https://arxiv.org/abs/2510.03600','mathdb-370772.json':'https://mathdb.com/api/posts/370772','stirling-v1.html':'https://arxiv.org/html/2507.18959v1','hankel-v1.html':'https://arxiv.org/html/2607.09376v1'}
def one(kv):
    name,url=kv
    try:
        r=requests.get(url,timeout=35);blob=r.content;ok=r.status_code==200 and (not name.endswith('.pdf') or blob.startswith(b'%PDF'))
        if ok:(p/name).write_bytes(blob)
        return {'name':name,'url':url,'status':r.status_code,'saved':ok,'sha256':hashlib.sha256(blob).hexdigest(),'bytes':len(blob)}
    except Exception as e:return {'name':name,'url':url,'error':str(e)}
with ThreadPoolExecutor(max_workers=4) as pool:records=list(pool.map(one,urls.items()))
(p/'retrievals.json').write_text(json.dumps({'date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'records':records},indent=2)+'\n')
for r in records:print(r['name'],r.get('status',r.get('error')),r.get('saved'))
