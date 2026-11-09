# Usage: python3 -I fetch.py ID URL [ID URL ...]  -- writes sources/<name>, receipts.jsonl (dated URL/status/sha256)
import sys,urllib.request,hashlib,json,datetime,pathlib,time
p=pathlib.Path(__file__).resolve().parent; src=p/'sources'; src.mkdir(exist_ok=True)
args=sys.argv[1:]
for name,url in zip(args[::2],args[1::2]):
    rec={'utc':datetime.datetime.now(datetime.UTC).isoformat(),'url':url,'file':'sources/'+name}
    try:
        req=urllib.request.Request(url,headers={'User-Agent':'research-fetch/1.0 (bounded; mj.kang research)'})
        with urllib.request.urlopen(req,timeout=60) as r:
            data=r.read(40_000_000); rec['status']=r.status; rec['content_type']=r.headers.get('Content-Type')
        (src/name).write_bytes(data); rec['sha256']=hashlib.sha256(data).hexdigest(); rec['bytes']=len(data)
    except Exception as e:
        rec['status']='error'; rec['error']=repr(e)[:300]
    with (p/'receipts.jsonl').open('a') as f: f.write(json.dumps(rec)+'\n')
    print(json.dumps(rec)); time.sleep(3)
