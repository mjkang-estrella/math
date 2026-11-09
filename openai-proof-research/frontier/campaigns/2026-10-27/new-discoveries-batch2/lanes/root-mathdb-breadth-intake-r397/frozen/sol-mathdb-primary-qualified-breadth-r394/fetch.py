from pathlib import Path
import urllib.request,urllib.error,json,hashlib,datetime
L=Path(__file__).resolve().parent;(L/'primary').mkdir(exist_ok=True)
for name,url in [('graph1','https://aimpl.org/graphstructureapp/1/'),('graph2','https://aimpl.org/graphstructureapp/2/'),('polypartition2','https://aimpl.org/polypartition/2/'),('zero1','https://aimpl.org/zeroforcing/1/')]:
 m=dict(url=url,requested_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),version='live retrieval; no release version advertised yet')
 try:
  with urllib.request.urlopen(url,timeout=25) as r:
   b=r.read(3000000);m.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),size=len(b));(L/'primary'/f'{name}.html').write_bytes(b)
 except Exception as e:m['failure']=repr(e)
 (L/'primary'/f'{name}.meta.json').write_text(json.dumps(m,indent=2)+'\n');print(m)
 if 'failure' in m:break
