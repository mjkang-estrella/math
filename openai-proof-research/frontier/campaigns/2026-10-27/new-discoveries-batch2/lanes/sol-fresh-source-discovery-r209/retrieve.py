from pathlib import Path
import urllib.request, urllib.error, hashlib, json, datetime, sys
L=Path(__file__).resolve().parent
url,name=sys.argv[1:]
utc=datetime.datetime.now(datetime.timezone.utc).isoformat()
r={'utc':utc,'url':url,'name':name}
try:
    with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathematicalResearch/1.0'}),timeout=40) as q:
        data=q.read(12000000);r.update(status=q.status,final_url=q.url,headers=dict(q.headers))
    for folder in ['sources','frozen']:(L/folder/name).write_bytes(data)
    r.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
    assert (L/'sources'/name).read_bytes()==(L/'frozen'/name).read_bytes()
except Exception as e:
    r.update(error=repr(e))
    if isinstance(e,urllib.error.HTTPError):
        data=e.read(200000);(L/'failures'/(name+'.body')).write_bytes(data);r['failure_sha256']=hashlib.sha256(data).hexdigest()
with (L/'http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
print(json.dumps(r))
