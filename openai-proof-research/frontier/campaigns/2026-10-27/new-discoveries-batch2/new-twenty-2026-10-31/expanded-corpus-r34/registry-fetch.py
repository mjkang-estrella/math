import urllib.request,hashlib,json,pathlib,datetime,resource
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(30,30))
L=pathlib.Path(__file__).resolve().parent;out=[]
for name,url in [('aim','https://aimath.robertj1.com/'),('whataifound','https://whataifound.org/')]:
 r=dict(name=name,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(url,timeout=20) as f:
   data=f.read(10000000);(L/'sources'/f'{name}.html').write_bytes(data);r.update(status=f.status,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
 except Exception as e:r['error']=str(e)
 out.append(r)
(L/'registry-fetch-receipts.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
