from pathlib import Path
import json,hashlib,resource,datetime,urllib.request,concurrent.futures,subprocess,time
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent;(p/'sources').mkdir(exist_ok=True)
records=json.loads((p/'provenance.json').read_text());jobs=[]
for id,e in records.items():
 a=e['parsed']['source_url'].rsplit('/',1)[1]
 for typ in ['abs','pdf']:jobs.append((a,typ))
def get(job):
 a,typ=job;u=f'https://arxiv.org/{typ}/{a}';out={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=18) as r:
   b=r.read(15*1024**2);out.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(p/'sources'/f'{a}.{typ}').write_bytes(b)
  if typ=='pdf':
   z=subprocess.run(['pdftotext','-layout',str(p/'sources'/f'{a}.pdf'),str(p/'sources'/f'{a}.txt')],capture_output=True,timeout=12);out['pdftotext_exit']=z.returncode
 except Exception as e:out['error']=str(e)
 return out
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool:
 out=list(pool.map(get,jobs))
(p/'fetch-receipts.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2));print(resource.getrusage(resource.RUSAGE_SELF))
