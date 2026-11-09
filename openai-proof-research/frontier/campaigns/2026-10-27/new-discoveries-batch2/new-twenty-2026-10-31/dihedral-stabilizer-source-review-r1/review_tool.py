import os,resource,time,json,hashlib,sys,re,urllib.request,urllib.error
from pathlib import Path
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
P=Path(__file__).resolve().parent; R=P.parent/'expanded-corpus-r325'; start=time.monotonic()
def record(n,data):
 f=P/n; f.write_text(json.dumps(data,indent=2)+'\n')
def read(n,a=0,b=None):
 assert '/' not in n and 'crown' not in n
 t=(R/n).read_text(); print('FILE',n,'totalchars',len(t),'range',a,b); print(t[a:b])
 inv=json.loads((P/'reads.json').read_text()) if (P/'reads.json').exists() else []
 inv.append({'file':str(R/n),'start':a,'end':b if b is not None else len(t),'total_chars':len(t),'sha256':hashlib.sha256((R/n).read_bytes()).hexdigest()});record('reads.json',inv)
def fetch(label,url):
 rec={'label':label,'url':url,'method':'GET','utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,method='GET'),timeout=18) as r:
   b=r.read(4500001);assert len(b)<=4500000
   rec.update(status=r.status,final_url=r.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(P/(label+'.raw')).write_bytes(b)
 except Exception as e: rec['error']=str(e)
 logs=json.loads((P/'HTTP-RECEIPTS.json').read_text()) if (P/'HTTP-RECEIPTS.json').exists() else [];logs.append(rec);record('HTTP-RECEIPTS.json',logs); print(json.dumps(rec))
try:
 exec(sys.argv[1])
finally:
 u=resource.getrusage(resource.RUSAGE_SELF); f=P/'resources.jsonl'
 with f.open('a') as q:q.write(json.dumps({'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'affinity':sorted(os.sched_getaffinity(0)),'wall_s':time.monotonic()-start,'CPU_s':u.ru_utime+u.ru_stime,'self_peak_RSS_KiB':u.ru_maxrss,'CPU_limit_s':120,'AS_bytes':6*1024**3,'group_cgroup_telemetry':'unavailable','job':'synchronous; external timeout <=140s'})+'\n')
