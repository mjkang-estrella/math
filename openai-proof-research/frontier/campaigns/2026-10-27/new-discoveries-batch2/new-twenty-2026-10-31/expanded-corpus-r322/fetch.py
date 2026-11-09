import os,resource,pathlib,sys,json,urllib.request,hashlib,datetime,time,concurrent.futures,html,re
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=pathlib.Path(__file__).parent
start=time.monotonic()
def get(spec):
 name,url=spec.split("=",1);r={"url":url,"utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"read_depth":"download only"}
 try:
  with urllib.request.urlopen(url,timeout=18) as f:
   b=f.read(12000001);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());assert len(b)<=12000000
  (p/(name+".html")).write_bytes(b)
  s=b.decode("utf-8",errors="replace");s=re.sub(r"<(script|style)\b[^>]*>.*?</\1>","",s,flags=re.S);s=re.sub(r"</(?:p|div|section|h[1-6]|li|tr)>","\n",s);s=html.unescape(re.sub("<[^>]+>"," ",s));s=re.sub(r"[ \t]+"," ",s);(p/(name+".txt")).write_text(s)
 except Exception as e:r.update(error=str(e),status=getattr(e,"code",None))
 (p/(name+".receipt.json")).write_text(json.dumps(r,indent=2));return name,r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 for name,r in pool.map(get,sys.argv[1:]):print(name,json.dumps(r))
print("RESOURCE",json.dumps({"wall_seconds":time.monotonic()-start,"self_rusage":list(resource.getrusage(resource.RUSAGE_SELF)),"affinity":sorted(os.sched_getaffinity(0)),"group_sampled_rss":"unavailable","children":"none"}))
