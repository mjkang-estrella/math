import urllib.request, pathlib,json,datetime,hashlib,resource,sys,signal,os
signal.alarm(55)
for key in ["OPENBLAS_NUM_THREADS","OMP_NUM_THREADS","MKL_NUM_THREADS","NUMEXPR_NUM_THREADS"]: os.environ[key]="1"
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(40,40))
b=pathlib.Path(__file__).parent
log=json.loads((b/'http.json').read_text()) if (b/'http.json').exists() else []
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 rec={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url,'file':'sources/'+name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-check/1.0'}),timeout=20) as r:
   data=r.read(16000000); rec.update(status=r.status,final_url=r.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest()); (b/'sources'/name).write_bytes(data)
 except Exception as e: rec['failure']=str(e)
 log.append(rec); print(name,rec.get('status',rec.get('failure')),rec.get('bytes'))
 (b/'http.json').write_text(json.dumps(log,indent=2)+'\n')
