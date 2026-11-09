import urllib.request,pathlib,json,hashlib,datetime,sys,resource
resource.setrlimit(resource.RLIMIT_CPU,(60,60))
L=pathlib.Path(__file__).resolve().parents[1]; (L/'sources/prior').mkdir(exist_ok=True)
for arg in sys.argv[1:]:
 name,url=arg.split('=',1)
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-review'}),timeout=20) as f:b=f.read();r.update(status=f.status,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  (L/'sources/prior'/name).write_bytes(b)
 except Exception as e:r['error']=str(e)
 (L/f'sources/prior/{name}-receipt.json').write_text(json.dumps(r,indent=2));print(name,r,flush=True)
