import pathlib,json,hashlib,resource,datetime,urllib.request,concurrent.futures,subprocess,re
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=pathlib.Path(__file__).resolve().parent;(p/'sources').mkdir(exist_ok=True)
r=json.loads((p/'reservation.json').read_text());jobs=[]
for o in r['rows']:
 a=o['source_url'].split('/')[-1];jobs.extend([(str(o['mathdb_id'])+'-abs','https://arxiv.org/abs/'+a),(str(o['mathdb_id'])+'-latest','https://arxiv.org/pdf/'+a)])
def fetch(job):
 name,url=job;out={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=8) as h:
   b=h.read(18000000);out.update(status=h.status,final_url=h.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  ext='.pdf' if b.startswith(b'%PDF') else '.html';f=p/'sources'/(name+ext);f.write_bytes(b);out['path']=str(f)
  if ext=='.pdf':
   q=subprocess.run(['pdftotext','-layout',str(f),str(f.with_suffix('.txt'))],capture_output=True,timeout=12);out['pdftotext_exit']=q.returncode
 except Exception as e:out['error']=str(e)
 return out

jobs=[]
for f in (p/"sources").glob("*-abs.html"):
 vs=sorted(set(re.findall(r"/abs/(\d+\.\d+v\d+)",f.read_text())))
 for v in vs[:-1]:jobs.append((f.stem.replace("-abs","")+"-"+v,"https://arxiv.org/pdf/"+v))

with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for out in ex.map(fetch,jobs):
  with (p/"source-receipts.jsonl").open("a") as f:f.write(json.dumps(out)+"\n")
  print(out["name"],out.get("status",out.get("error")),flush=True)
