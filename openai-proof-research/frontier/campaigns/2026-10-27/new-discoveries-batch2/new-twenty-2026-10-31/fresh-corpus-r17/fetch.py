from pathlib import Path
import requests, json, hashlib, datetime, concurrent.futures, subprocess, resource, os
P=Path(__file__).resolve().parent; (P/'sources').mkdir(exist_ok=True)
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
r=json.loads((P/'inputs/literal-records.json').read_text())
urls={v['record']['source_url'].replace('/abs/','/pdf/') for v in r.values()}
urls.add('https://api.github.com/repos/openai/math/commits/main')
def get(url):
 name=url.rsplit('/',1)[-1]+('.json' if 'github' in url else '.pdf'); f=P/'sources'/name
 try:
  a=requests.get(url,timeout=35);f.write_bytes(a.content)
  receipt={'url':url,'final_url':a.url,'observed':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':a.status_code,'sha256':hashlib.sha256(a.content).hexdigest(),'file':str(f.relative_to(P))}
  if a.status_code==200 and a.content.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(f),str(f.with_suffix('.txt'))],check=True)
  return receipt
 except Exception as e:return {'url':url,'error':str(e)}
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex: rows=list(ex.map(get,sorted(urls)))
(P/'sources/receipts.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))
