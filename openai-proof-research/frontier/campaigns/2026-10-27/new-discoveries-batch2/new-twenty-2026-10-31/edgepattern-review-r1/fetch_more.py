from pathlib import Path
import json,urllib.request,hashlib,datetime,resource,os
resource.setrlimit(resource.RLIMIT_CPU,(120,120));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
out=Path(__file__).resolve().parent/'live'
urls={'occupancy.pdf':'https://arxiv.org/pdf/2003.14361','author.html':'https://perso.lisn.upsaclay.fr/fpirot/'}
for n,url in urls.items():
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathDB-independent-review/1.0'}),timeout=25) as f:
   data=f.read(15000000);r.update(status=f.status,sha256=hashlib.sha256(data).hexdigest());(out/n).write_bytes(data)
 except Exception as e:r['error']=str(e)
 (out/(n+'.receipt.json')).write_text(json.dumps(r,indent=2));print(r)
