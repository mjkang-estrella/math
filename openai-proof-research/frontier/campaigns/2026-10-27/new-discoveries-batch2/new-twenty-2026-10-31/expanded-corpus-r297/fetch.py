import os,resource,pathlib,json,urllib.request,urllib.error,hashlib,datetime,sys,subprocess,time
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
l=pathlib.Path(__file__).parent;(l/'http').mkdir(exist_ok=True)
for label,url in json.loads(sys.argv[1]):
 t=time.monotonic();r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'read_depth':'fetched only; see read inventory'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical research source reader'}),timeout=18) as f:
   data=f.read(16000001);r.update(status=f.status,final_url=f.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest());assert len(data)<=16000000
  (l/'http'/label).write_bytes(data)
  if data.startswith(b'%PDF'):
   z=subprocess.run(['pdftotext','-layout',str(l/'http'/label),str(l/'http'/(label+'.txt'))],timeout=20,capture_output=True);r['pdftotext_exit']=z.returncode
 except Exception as e:r.update(error=str(e),status=getattr(e,'code',None))
 r['elapsed_seconds']=time.monotonic()-t;(l/'http'/(label+'.receipt.json')).write_text(json.dumps(r,indent=2)+'\n');print(label,json.dumps(r),flush=True)
