import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,sys,time,json,urllib.request,hashlib,re,datetime
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));import review_ops as r
logs=[];jobs=[]
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 t=time.time(); rec=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(url,timeout=20) as q:
   b=q.read(3000000);rec.update(status=q.status,finalURL=q.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()); s=b.decode();jobs.append(r.write('live/'+name,s))
   print(name,'currentOid',re.findall(r'"currentOid":"([a-f0-9]{40})"',s)[:3])
   if name.endswith('.lean'): print(s)
   else:
    for l in s.splitlines():
     if re.search('citation_doi|citation_journal|Submitted on|last revised|Journal of Algebraic|s10801|correction|erratum',l,re.I):print(l[:2000])
 except Exception as e:rec.update(error=repr(e))
 rec['wall']=time.time()-t; logs.append(rec);print(json.dumps(rec))
jobs.append(r.write('http-'+str(time.time_ns())+'.json',json.dumps(dict(HTTP=logs,jobs=jobs,resource=dict(affinity=sorted(os.sched_getaffinity(0)),usage=list(resource.getrusage(resource.RUSAGE_SELF)))),indent=2)));print(json.dumps(jobs));r.finish('live-'+str(time.time_ns()))
