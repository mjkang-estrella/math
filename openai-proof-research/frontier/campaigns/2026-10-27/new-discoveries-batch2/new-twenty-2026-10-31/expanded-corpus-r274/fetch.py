import json,hashlib,datetime,resource,urllib.request,urllib.error,concurrent.futures,subprocess,sys,time
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent; out=p/'sources'; out.mkdir(exist_ok=True)
records=json.loads((p/'literal-records.json').read_text()); urls=[]
if len(sys.argv)>1: urls=sys.argv[1:]
else:
 for a in records.values():
  u=a['record']['source_url']; urls.extend([u,u.replace('/abs/','/pdf/')])
def get(u):
 name=u.split('://')[1].replace('/','_').replace('?','_'); dst=out/name; receipt={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 if dst.exists():return
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Research source verification'}),timeout=12) as r:
   b=r.read(20*1024**2); receipt.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),file=str(dst.relative_to(p))); dst.write_bytes(b)
   if b.startswith(b'%PDF'): subprocess.run(['pdftotext','-layout',str(dst),str(dst)+'.txt'],check=True,timeout=15)
 except Exception as e:receipt['error']=str(e)
 (out/(name+'.receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt),flush=True)
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:list(ex.map(get,dict.fromkeys(urls)))
