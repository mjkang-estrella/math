import os,resource,json,hashlib,datetime,concurrent.futures,urllib.request,subprocess,re,time
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).parent;s=p/'sources';s.mkdir(exist_ok=True)
records=json.loads((p/'raw-records.json').read_text()); urls=sorted(set(v['record']['source_url'] for v in records.values()))
def fetch(url):
 name=url.split('/')[-1]; dest=s/('abs-'+name+'.html'); start=datetime.datetime.now(datetime.timezone.utc).isoformat();r={'url':url,'utc':start}
 try:
  with urllib.request.urlopen(url,timeout=12) as f: b=f.read(12_000_000);r.update(status=f.status,final_url=f.url)
  dest.write_bytes(b);r.update(path=str(dest),sha256=hashlib.sha256(b).hexdigest())
 except Exception as e:r['error']=str(e)
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex: rec=list(ex.map(fetch,urls))
(s/'abs-receipts.json').write_text(json.dumps(rec,indent=2)+'\n')
print(json.dumps(rec,indent=2))
