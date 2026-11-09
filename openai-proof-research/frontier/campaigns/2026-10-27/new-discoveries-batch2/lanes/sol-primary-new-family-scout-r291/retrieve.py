from run import *
import urllib.request,urllib.error,sys
u=sys.argv[1]; n=sys.argv[2]
assert not any(x in u.lower() for x in ['google','github','sciencedirect'])
p=L/'primary'/n;p.parent.mkdir(exist_ok=True)
assert not p.exists()
r={'url':u,'time':datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
 with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Mathematical research; bounded public source retrieval'}),timeout=35) as f:
  data=f.read(12000001);assert len(data)<=12000000
  p.write_bytes(data);r.update(status=f.status,bytes=len(data),sha256=sha(p),frozen_before_read=True)
except Exception as e:r['failure']=str(e)
with (L/'access.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
print(r)
