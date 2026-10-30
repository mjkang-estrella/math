from pathlib import Path
import sys, urllib.request, json, hashlib, datetime
P=Path(__file__).resolve().parent
for n,u in zip(sys.argv[1::2],sys.argv[2::2]):
    r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':u,'file':n}
    try:
        z=urllib.request.urlopen(u,timeout=25); raw=z.read(8000000)
        (P/'retrieved'/n).write_bytes(raw)
        r.update(status=z.status,final_url=z.url,bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())
    except Exception as e: r['error']=str(e)
    with (P/'retrieval.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
    print(r,flush=True)
