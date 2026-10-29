import urllib.request,json,hashlib,datetime,pathlib,sys,resource,signal
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));resource.setrlimit(resource.RLIMIT_CPU,(40,40));signal.alarm(55)
b=pathlib.Path(__file__).resolve().parent
log=json.loads((b/'http.json').read_text()) if (b/'http.json').exists() else []
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':'sources/'+name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-check/1.0'}),timeout=12) as f:
   data=f.read(20000000);r.update(status=f.status,final_url=f.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest());(b/'sources'/name).write_bytes(data)
 except Exception as e:r['error']=str(e)
 log.append(r);print(json.dumps(r));(b/'http.json').write_text(json.dumps(log,indent=2))
