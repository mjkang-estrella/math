import os,resource,json,hashlib,datetime,concurrent.futures,urllib.request,subprocess,re,time
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).parent;s=p/'sources';s.mkdir(exist_ok=True)
jobs=[]; versions={}
for f in sorted(s.glob('abs-*.html')):
 a=f.stem[4:];text=f.read_text();vs=sorted(set(re.findall(r'\[v(\d+)\]',text)),key=int); versions[a]=vs
 for v in vs:jobs.append(('https://arxiv.org/pdf/'+a+'v'+v,a+'v'+v))
(p/'versions.json').write_text(json.dumps(versions,indent=2))
def fetch(job):
 url,name=job;dest=s/(name+'.pdf');r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=8) as f:b=f.read(12_000_000);r.update(status=f.status,final_url=f.url)
  dest.write_bytes(b);r.update(path=str(dest),sha256=hashlib.sha256(b).hexdigest())
  if b.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(dest),str(s/(name+'.txt'))],timeout=12,check=True)
 except Exception as e:r['error']=str(e)
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex: rec=list(ex.map(fetch,jobs))
(s/'pdf-receipts.json').write_text(json.dumps(rec,indent=2)+'\n');print('PDF jobs',len(jobs),'errors',[r for r in rec if 'error' in r])
