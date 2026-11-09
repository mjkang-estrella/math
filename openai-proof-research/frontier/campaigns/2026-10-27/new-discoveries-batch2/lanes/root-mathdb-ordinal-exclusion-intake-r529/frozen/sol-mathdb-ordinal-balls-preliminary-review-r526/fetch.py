import urllib.request,urllib.error,json,hashlib,datetime,pathlib
D=pathlib.Path(__file__).resolve().parent
jobs=[('echeloned-published.pdf','https://www.cambridge.org/core/services/aop-cambridge-core/content/view/2A35174EF5425D30946E008CB31FB4AE/S2050509425000477a.pdf/div-class-title-echeloned-spaces-div.pdf'),('ordinal-published.html','https://link.springer.com/article/10.1007/s10474-019-00972-z')]
r=[]
for name,url in jobs:
 e=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),path=name)
 try:
  with urllib.request.urlopen(url,timeout=35) as f: b=f.read(7000000);e.update(status=f.status,final_url=f.url)
  (D/name).write_bytes(b);e.update(size=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as ex:e['failure']=str(ex)
 r.append(e)
(D/'retrieval-bindings.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
