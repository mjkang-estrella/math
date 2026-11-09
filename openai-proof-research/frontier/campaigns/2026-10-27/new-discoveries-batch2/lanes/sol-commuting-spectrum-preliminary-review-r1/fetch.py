import urllib.request,urllib.error,sys,json,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent
u,name=sys.argv[1:];p=L/'retrieved'/name;p.parent.mkdir(exist_ok=True)
try:
 with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Mathematical-source-review/1.0'}),timeout=30) as r:
  d=r.read(6000000);status=r.status;final=r.url
except urllib.error.HTTPError as e:
 d=e.read(100000);status=e.code;final=e.url
except Exception as e:
 d=str(e).encode();status='error';final=u
assert not p.exists();p.write_bytes(d)
rec=dict(url=u,final_url=final,status=status,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),path=str(p),bytes=len(d),sha256=hashlib.sha256(d).hexdigest(),frozen_before_read=True)
with (L/'access.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
print(json.dumps(rec))
