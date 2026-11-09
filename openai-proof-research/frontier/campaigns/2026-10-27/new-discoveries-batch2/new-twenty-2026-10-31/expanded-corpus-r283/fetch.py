from pathlib import Path
import json,urllib.request,hashlib,datetime,concurrent.futures,resource,sys
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent;s=p/'sources';s.mkdir(exist_ok=True)
r=json.loads((p/'reservation.json').read_text());jobs=[]
for d in r['rows']:
 u=d['source_url'];i=str(d['mathdb_id'])
 if 'arxiv.org/abs/' in u:
  aid=u.split('/abs/')[1];jobs.extend([(i+'-abs',u),(i+'-pdf','https://arxiv.org/pdf/'+aid)])
 elif 'github.com' in u:jobs.append((i+'-lean',u.replace('https://github.com/','https://raw.githubusercontent.com/').replace('/blob/','/')))
 else:jobs.append((i+'-page',u))
if len(sys.argv)>1: jobs=json.loads(Path(sys.argv[1]).read_text())
def fetch(job):
 name,u=job;rec={'name':name,'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'ResearchSourceReview/1.0'}),timeout=12) as a:
   b=a.read(20000000);rec.update(status=a.status,final_url=a.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(s/name).write_bytes(b)
 except Exception as e:rec.update(error=str(e))
 with (p/'receipts.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 return name,rec.get('status',rec.get('error'))
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for result in ex.map(fetch,jobs): print(*result,flush=True)
