import urllib.request,pathlib,json,datetime,hashlib
L=pathlib.Path(__file__).resolve().parent;log=[]
for key,u in [('ascent-successor','https://arxiv.org/html/1207.3755'),('123-successor','https://arxiv.org/html/2303.02611'),('sensitivity-successor','https://arxiv.org/html/1907.00847'),('planar-successor','https://arxiv.org/html/1904.05269')]:
 try:
  r=urllib.request.urlopen(u,timeout=20);b=r.read();p=L/'sources'/(key+'.html');p.write_bytes(b);log.append(dict(key=key,url=u,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),path=str(p)))
 except Exception as e:log.append(dict(key=key,url=u,failure=str(e)))
(L/'successor-receipts.json').write_text(json.dumps(log,indent=2)+'\n')
