import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,sys,json,time,datetime,re,hashlib
L=pathlib.Path(__file__).resolve().parent; run=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%f'); start=time.monotonic(); code=0
try:
 p=(L/'sources'/sys.argv[1]).resolve(); assert p.is_relative_to(L); t=p.read_text(); out=[]
 for spec in sys.argv[2:]:
  if spec.startswith('@'):
   a,z=map(int,spec[1:].split(':')); out.append(dict(start=a,end=z,text=t[a:z]))
  else:
   hits=list(re.finditer(spec,t,re.I)); out.append(dict(pattern=spec,count=len(hits),hits=[dict(start=m.start(),text=t[max(0,m.start()-100):m.end()+250]) for m in hits][:35]))
 obj=dict(source=str(p),sha256=hashlib.sha256(t.encode()).hexdigest(),read=out); (L/('read-excerpts/'+run+'.json')).write_text(json.dumps(obj,indent=2)); print(json.dumps(obj,ensure_ascii=False))
except:code=1; raise
finally:
 u=resource.getrusage(resource.RUSAGE_SELF); (L/('receipts/process-read-'+run+'.json')).write_text(json.dumps(dict(exit_code=code,wall_s=time.monotonic()-start,affinity=sorted(os.sched_getaffinity(0)),CPU_limit=120,AS_limit=6*1024**3,self_peak_RSS_KiB=u.ru_maxrss,self_CPU_s=u.ru_utime+u.ru_stime,external_wall_timeout=140,limitation='Self high-water only')))
