import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(100,100))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,subprocess,sys,time,datetime,urllib.request,re
P=pathlib.Path(__file__).resolve().parent
Q=P.parent/'expanded-corpus-r361'
start=time.monotonic(); reads=[]; accesses=[]
def write(n,s):
 r=subprocess.run([sys.executable,'-I','-B',str(P/'write_lane.py'),n],input=s,text=True,capture_output=True); assert r.returncode==0,r.stderr
def read(n,a,b):
 p=Q/n; data=p.read_bytes(); s=data.decode(); excerpt=s[a:b]; reads.append(dict(path=str(p),sha256=hashlib.sha256(data).hexdigest(),start=a,end=min(b,len(s)),depth='Only recorded character excerpt read; full bytes hashed, not full body reviewed')); print(n,a,b); print(excerpt); write('excerpts/'+p.name+f'.{a}.txt',excerpt)
read('sources/derived.html.txt',15500,18800)
read('sources/derived.html.txt',46500,49300)
read('sources/derived-v1.html.txt',0,1600)
s=(Q/'sources/derived-v1.html.txt').read_text(); i=s.find('Conjecture 8.5'); read('sources/derived-v1.html.txt',i-800,i+1100)
read('sources/maximal-matroids.html.txt',1700,5700)
# Journal extraction uses existing PDF, stdout only; subprocess reaped; caps inherited.
p=Q/'sources/derived-journal.pdf'; data=p.read_bytes()
r=subprocess.run(['pdftotext','-f','2','-l','4',str(p),'-'],capture_output=True,text=True); assert r.returncode==0
write('excerpts/journal-pages2-4.txt',r.stdout); print(r.stdout)
r=subprocess.run(['pdftotext','-f','22','-l','23',str(p),'-'],capture_output=True,text=True); assert r.returncode==0
write('excerpts/journal-pages22-23.txt',r.stdout); print(r.stdout)
reads.append(dict(path=str(p),sha256=hashlib.sha256(data).hexdigest(),depth='Text extraction pages 2-4 and 22-23; no figures or full-body review',pdftotext_exits=[0,0]))
for name,url in [('arxiv-abs','https://arxiv.org/abs/2206.06881'),('author-update','https://matroidunion.org/?p=5265'),('openai-head','https://github.com/openai/math'),('leanpool-head','https://github.com/LeanPool/LeanPool')]:
 t=time.monotonic(); rec=dict(name=name,url=url,method='GET',utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(url,timeout=20) as f:
   d=f.read(2500000); rec.update(status=f.status,final_url=f.url,bytes=len(d),sha256=hashlib.sha256(d).hexdigest())
  write('sources/'+name+'.html',d.decode('utf-8',errors='replace')); rec['depth']='Acquired only; relevant text surfaced separately'
  # routing snippets only, not proof absence
  plain=re.sub('<[^>]*>',' ',d.decode('utf-8',errors='replace')); matches=[]
  for term in ['Conjecture','generic','still open','Section 6','commit/','currentOid']:
   for m in list(re.finditer(re.escape(term),plain))[:3]: matches.append(plain[max(0,m.start()-120):m.start()+400])
  print(name,json.dumps(matches)); rec['surfaced_snippets']=matches
 except Exception as e: rec.update(error=type(e).__name__+': '+str(e),status=getattr(e,'code',None),final_url=url,bytes=0,depth='Failure; no body read; no retry')
 rec['wall_seconds']=time.monotonic()-t; accesses.append(rec)
write('read-inventory.json',json.dumps(reads,indent=2)+'\n'); write('access-receipts.json',json.dumps(accesses,indent=2)+'\n')
u=resource.getrusage(resource.RUSAGE_SELF); c=resource.getrusage(resource.RUSAGE_CHILDREN)
write('source-job-receipt.json',json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),exit=0,caps_before_reads=True,affinity=sorted(os.sched_getaffinity(0)),cpu_limit=100,as_limit=6*1024**3,self_user=u.ru_utime,self_system=u.ru_stime,self_maxrss_KiB=u.ru_maxrss,reaped_child_user=c.ru_utime,reaped_child_system=c.ru_stime,wall_seconds=time.monotonic()-start,telemetry_scope='self rusage and reaped child CPU; no group peak claimed',children_reaped=True),indent=2)+'\n')
