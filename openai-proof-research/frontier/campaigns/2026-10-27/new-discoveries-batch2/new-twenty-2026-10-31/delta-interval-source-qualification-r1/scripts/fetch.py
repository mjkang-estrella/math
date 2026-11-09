import concurrent.futures,datetime,hashlib,json,resource,subprocess,urllib.request
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
jobs=json.loads(Path('fetch-list.json').read_text())
def fetch(j):
 n,u=j; r=dict(name=n,url=u,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'MathSourceAudit/1.0'}),timeout=25) as f: data=f.read(22000000);r.update(status=f.status,final_url=f.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
  Path('sources',n).write_bytes(data)
  if data.startswith(b'%PDF'):r['pdftotext']=subprocess.run(['pdftotext','-layout','sources/'+n,'sources/'+n+'.txt'],timeout=20).returncode
 except Exception as e:r['error']=str(e)
 Path('receipts',n+'.json').write_text(json.dumps(r,indent=2)+'\n');return r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for r in ex.map(fetch,jobs):print(json.dumps(r))
