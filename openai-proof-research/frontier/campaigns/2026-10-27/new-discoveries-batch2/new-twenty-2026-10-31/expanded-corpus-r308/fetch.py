import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import sys,json,time,hashlib,urllib.request,urllib.error,concurrent.futures
from pathlib import Path
P=Path(__file__).resolve().parent
def fetch(pair):
 name,url=pair; start=time.time(); rec={'name':name,'url':url,'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source review (public read only)'}),timeout=18) as f:
   b=f.read(16000001);assert len(b)<=16000000
   rec.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(P/'sources'/name).write_bytes(b)
 except Exception as e:rec.update(error=str(e),status=getattr(e,'code',None))
 rec['wall_s']=round(time.time()-start,3)
 with (P/'http-receipts.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 return rec
(P/'sources').mkdir(exist_ok=True)
if sys.argv[1]=='initial':
 rows=json.loads((P/'reservation.json').read_text())['rows']
 jobs=[(str(r['mathdb_id'])+'-abs.html',r['source_url']) for r in rows]
 jobs += [('openai-current.html','https://github.com/openai/math'),('openai-current-CONTENTS.md','https://raw.githubusercontent.com/openai/math/main/CONTENTS.md'),('leanpool-projects.yml','https://raw.githubusercontent.com/Vilin97/lean-pool/main/LeanPool/projects.yml'),('leanpool-index.lean','https://raw.githubusercontent.com/Vilin97/lean-pool/main/LeanPool.lean')]
else:jobs=json.loads((P/sys.argv[1]).read_text())
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for r in ex.map(fetch,jobs):print(json.dumps(r))
