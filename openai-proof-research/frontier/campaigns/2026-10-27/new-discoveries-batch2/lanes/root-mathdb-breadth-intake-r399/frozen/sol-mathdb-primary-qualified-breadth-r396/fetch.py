from pathlib import Path
import urllib.request,urllib.error,datetime,hashlib,json
R=Path(__file__).parent;(R/'evidence').mkdir(exist_ok=True)
items=[('graphstructure-2','https://aimpl.org/graphstructureapp/2/'),('graphstructure-3','https://aimpl.org/graphstructureapp/3/'),('freebycyclic-1','https://aimpl.org/freebycyclic/1/')]
log=[]
for name,url in items:
 row={'requested_url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'method':'public HTTPS urllib; no TLS bypass, no retries'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source qualification'}),timeout=25) as r:
   data=r.read(3000000);row.update(status=r.status,final_url=r.url,headers=dict(r.headers))
  p=R/'evidence'/f'{name}.html';p.write_bytes(data);row.update(path=str(p.relative_to(R)),size=len(data),sha256=hashlib.sha256(data).hexdigest())
 except Exception as e:row.update(error=repr(e),status=getattr(e,'code',None))
 log.append(row);(R/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n');print(json.dumps(row))
 if row.get('status') in [403,429] or 'challenge' in str(row).lower():break
