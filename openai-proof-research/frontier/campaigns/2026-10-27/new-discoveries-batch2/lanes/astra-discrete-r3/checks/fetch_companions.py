from pathlib import Path
import urllib.request, hashlib, json, datetime
from concurrent.futures import ThreadPoolExecutor
out=Path(__file__).resolve().parents[1]/'sources'
items=[('universal-subspaces','https://arxiv.org/pdf/0802.1915v3'),('ideosphere-zero','https://ideosphere.ai/papers/zero-pattern-inner-v1.pdf'),('moving-zeros','https://www.csun.edu/~asethura/papers/SimultHess4AuthorsRevised.pdf')]
def get(item):
    name,url=item
    r={'name':name,'url':url,'accessed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    try:
        with urllib.request.urlopen(url,timeout=35) as f:
            data=f.read();r['status']=f.status
        if data.startswith(b'%PDF'):
            (out/(name+'.pdf')).write_bytes(data);r['sha256']=hashlib.sha256(data).hexdigest();r['file']=name+'.pdf'
        else:r['error']='Not PDF; no alternate access attempted'
    except Exception as e:r['error']=str(e)
    return r
with ThreadPoolExecutor(max_workers=3) as pool: result=list(pool.map(get,items))
(out/'companion-manifest.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
