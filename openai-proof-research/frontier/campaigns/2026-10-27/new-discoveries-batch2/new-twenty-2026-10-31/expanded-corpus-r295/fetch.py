import urllib.request,urllib.error,json,hashlib,datetime,concurrent.futures,resource,time,os,sys
from pathlib import Path
L=Path(__file__).parent;(L/"http").mkdir(exist_ok=True)
jobs=[]
if len(sys.argv)>1: jobs=json.loads((L/sys.argv[1]).read_text())
else:
 for d in json.loads((L/"reservation.json").read_text())["rows"]:
  jobs.append((str(d["mathdb_id"])+".abs",d["source_url"]))
  if d["mathdb_id"] in [364196,329383,367412,339902,325559,373097,381617]:jobs.append((str(d["mathdb_id"])+".pdf",d["source_url"].replace("/abs/","/pdf/")))
 jobs += [("openai.html","https://github.com/openai/math"),("aim.html","https://github.com/the-omega-institute/trureturing"),("pool.html","https://github.com/LeanPool/lean-pool")]
def fetch(job):
 name,url=job;rec={"name":name,"url":url,"utc":datetime.datetime.now(datetime.timezone.utc).isoformat()};t=time.monotonic();b=b""
 try:
  with urllib.request.urlopen(url,timeout=8) as f:b=f.read(16000000);rec.update(status=f.status,final_url=f.url)
 except urllib.error.HTTPError as e:b=e.read(100000);rec.update(status=e.code,error=str(e))
 except Exception as e:rec.update(status=None,error=str(e))
 (L/"http"/name).write_bytes(b);rec.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),wall=time.monotonic()-t);return rec
start=time.monotonic()
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 for rec in pool.map(fetch,jobs):
  with (L/"http-receipts.jsonl").open("a") as f:f.write(json.dumps(rec)+"\n")
  print(rec["name"],rec["status"],rec["bytes"],flush=True)
with (L/"process-resources.jsonl").open("a") as f:f.write(json.dumps({"argv":sys.argv,"affinity":sorted(os.sched_getaffinity(0)),"rlimit_as":resource.getrlimit(resource.RLIMIT_AS),"rlimit_cpu":resource.getrlimit(resource.RLIMIT_CPU),"maxrss_kib":resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,"wall":time.monotonic()-start,"all_joined":True})+"\n")
