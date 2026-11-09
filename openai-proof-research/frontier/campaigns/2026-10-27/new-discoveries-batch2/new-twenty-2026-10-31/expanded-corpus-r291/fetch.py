import urllib.request,urllib.error,json,hashlib,datetime,concurrent.futures,resource,time,os
from pathlib import Path
L=Path(__file__).parent; (L/"http").mkdir(exist_ok=True)
r=json.loads((L/"reservation.json").read_text()); jobs=[]
for d in r["rows"]:
 aid=d["source_url"].split("/abs/")[-1]
 jobs.append((str(d["mathdb_id"])+".abs",d["source_url"]))
 if d["mathdb_id"] in [359776,360815,375521,365127,375206,356243,352904,367474,357501]: jobs.append((str(d["mathdb_id"])+".pdf","https://arxiv.org/pdf/"+aid))
jobs += [("openai-current.html","https://github.com/openai/math"),("aim-current.html","https://github.com/the-omega-institute/trureturing"),("pool-current.html","https://github.com/LeanPool/lean-pool"),("pool-projects.yml","https://raw.githubusercontent.com/LeanPool/lean-pool/main/LeanPool/projects.yml")]
def fetch(job):
 name,url=job; rec={"name":name,"url":url,"utc":datetime.datetime.now(datetime.timezone.utc).isoformat()}; start=time.monotonic();b=b""
 try:
  with urllib.request.urlopen(url,timeout=9) as f: b=f.read(16000000);rec.update(status=f.status,final_url=f.url)
 except urllib.error.HTTPError as e: b=e.read(100000);rec.update(status=e.code,error=str(e))
 except Exception as e: rec.update(status=None,error=str(e))
 (L/"http"/name).write_bytes(b);rec.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),wall_seconds=time.monotonic()-start)
 return rec
start=time.monotonic()
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 for rec in pool.map(fetch,jobs):
  with (L/"http-receipts.jsonl").open("a") as f:f.write(json.dumps(rec)+"\n")
  print(rec["name"],rec["status"],rec["bytes"],flush=True)
(L/"fetch-resources.json").write_text(json.dumps({"affinity":sorted(os.sched_getaffinity(0)),"rlimit_as":resource.getrlimit(resource.RLIMIT_AS),"rlimit_cpu":resource.getrlimit(resource.RLIMIT_CPU),"maxrss_kib":resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,"wall_seconds":time.monotonic()-start,"workers":2,"all_joined":True},indent=2))
