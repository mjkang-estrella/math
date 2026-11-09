import os,sys,json,hashlib,datetime,urllib.request,urllib.error,resource,socket
from pathlib import Path
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
socket.setdefaulttimeout(20)
D=Path(__file__).resolve().parents[1]
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathDB-independent-review/1.0'}),timeout=20) as r:
   data=r.read(15000000);receipt.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));(D/'downloads'/name).write_bytes(data)
 except Exception as e: receipt.update(error=str(e),status=getattr(e,'code',None))
 receipt['peak_rss_kib']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
 (D/'receipts'/(name+'.json')).write_text(json.dumps(receipt,indent=2));print(name,json.dumps(receipt),flush=True)
