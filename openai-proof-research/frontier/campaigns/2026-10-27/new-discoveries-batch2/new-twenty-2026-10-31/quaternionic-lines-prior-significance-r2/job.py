import os,resource,time,json,sys,hashlib,urllib.request,datetime,subprocess
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6442450944,6442450944))
p=__import__("pathlib").Path(__file__).resolve().parent
start=time.monotonic()
def fetch(url):
 r={"url":url,"method":"GET","utc":str(datetime.datetime.now(datetime.timezone.utc))}
 try:
  with urllib.request.urlopen(url,timeout=18) as f:
   b=f.read(16000000); r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  ext="pdf" if b.startswith(b"%PDF") else "html"
  dest=p/"sources"/(hashlib.sha256(url.encode()).hexdigest()[:16]+"."+ext); dest.parent.mkdir(exist_ok=True); dest.write_bytes(b); r["path"]=str(dest.relative_to(p))
  if ext=="pdf":
   subprocess.run(["pdftotext","-layout",str(dest),str(dest.with_suffix(".txt"))],timeout=20,check=True); r["text_path"]=str(dest.with_suffix(".txt").relative_to(p))
 except Exception as e:r["error"]=str(e)
 with (p/"http-receipts.jsonl").open("a") as f:f.write(json.dumps(r)+"\n")
 print(json.dumps(r),flush=True)
try:
 for url in sys.argv[1:]:fetch(url)
finally:
 u=resource.getrusage(resource.RUSAGE_SELF)
 with (p/"resource-jobs.jsonl").open("a") as f:f.write(json.dumps({"argv":sys.argv,"wall_s":time.monotonic()-start,"self_CPU_s":u.ru_utime+u.ru_stime,"self_peak_RSS_KiB":u.ru_maxrss,"affinity":sorted(os.sched_getaffinity(0)),"limits":"CPU120 AS6GiB external wall<=140; child pdftotext inherits caps, synchronously reaped; not aggregate/group/cgroup telemetry"})+"\n")
