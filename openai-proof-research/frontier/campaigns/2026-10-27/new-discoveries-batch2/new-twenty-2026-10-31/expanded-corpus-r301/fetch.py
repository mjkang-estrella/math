import os,resource,sys,json,urllib.request,hashlib,datetime,concurrent.futures,subprocess,time
from pathlib import Path
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
l=Path(__file__).parent
def fetch(kv):
 k,u=kv;r={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact':'sources/'+k};start=time.monotonic()
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Research-source-review/1.0'}),timeout=8) as q:r['status']=q.status;data=q.read(16000000);r['final_url']=q.url
  (l/'sources'/k).write_bytes(data);r.update(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
  if data.startswith(b'%PDF'):
   z=subprocess.run(['pdftotext','-layout',str(l/'sources'/k),str(l/'sources'/(k+'.txt'))],capture_output=True,timeout=8);r['pdftotext_rc']=z.returncode
 except Exception as e:r['error']=str(e)
 r['wall_seconds']=time.monotonic()-start
 (l/'sources'/(k+'.receipt.json')).write_text(json.dumps(r,indent=2));return r
urls=json.loads((l/sys.argv[1]).read_text())
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for r in ex.map(fetch,urls.items()):print(r['artifact'],r.get('status',r.get('error')),r.get('bytes'),flush=True)
