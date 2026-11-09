import urllib.request,urllib.error,pathlib,sys,json,hashlib,datetime,resource
resource.setrlimit(resource.RLIMIT_AS,(1024**3,)*2);resource.setrlimit(resource.RLIMIT_CPU,(30,30))
w=pathlib.Path(__file__).resolve().parent; (w/'sources').mkdir(exist_ok=True)
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 rec=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical research (public sources)'}),timeout=35) as r:
   data=r.read(18000000);rec.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));(w/'sources'/name).write_bytes(data)
 except Exception as e: rec.update(error=str(e))
 (w/'sources'/(name+'.receipt.json')).write_text(json.dumps(rec,indent=2)); print(name,rec)
