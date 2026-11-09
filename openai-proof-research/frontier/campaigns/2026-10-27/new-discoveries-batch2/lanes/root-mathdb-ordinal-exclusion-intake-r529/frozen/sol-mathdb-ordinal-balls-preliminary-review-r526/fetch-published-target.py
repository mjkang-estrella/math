import urllib.request,urllib.error,json,hashlib,datetime,pathlib
D=pathlib.Path(__file__).resolve().parent
jobs=[('ordinal-published.pdf','https://link.springer.com/content/pdf/10.1007/s10474-019-00972-z.pdf')]
r=[]
for name,url in jobs:
 e=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),path=name)
 try:
  with urllib.request.urlopen(url,timeout=35) as f: b=f.read(7000000);e.update(status=f.status,final_url=f.url)
  (D/name).write_bytes(b);e.update(size=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as ex:e['failure']=str(ex)
 r.append(e)
(D/'published-target-bindings.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
