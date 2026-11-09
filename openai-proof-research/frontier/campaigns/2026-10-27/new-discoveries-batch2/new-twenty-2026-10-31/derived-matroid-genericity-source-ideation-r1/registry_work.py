import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(100,100)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,sys,subprocess,json,re,urllib.request,datetime,time,hashlib
P=pathlib.Path(__file__).resolve().parent; receipts=[]; start=time.monotonic()
def wr(n,s):
 r=subprocess.run([sys.executable,'-I','-B',str(P/'write_lane.py'),n],input=s,text=True,capture_output=True); assert r.returncode==0
for n,url in [('openai-contents','https://raw.githubusercontent.com/openai/math/4eaee87548250b2682affda7d05d947c05554bae/CONTENTS.md'),('leanpool-correct-head','https://github.com/LeanPool/lean-pool')]:
 rec=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),url=url,method='GET'); t=time.monotonic()
 try:
  with urllib.request.urlopen(url,timeout=20) as f: d=f.read(3000000); rec.update(status=f.status,final_url=f.url,bytes=len(d),sha256=hashlib.sha256(d).hexdigest())
  s=d.decode(); wr('sources/'+n+'.txt',s)
  rec['depth']='Routing catalog/metadata only; not proof-body clearance'
  rec['target_lines']=[x for x in s.splitlines() if any(k in x.lower() for k in ['derived matroid','derived-matroid','355016'])] if n=='openai-contents' else re.findall(r'currentOid.{0,65}',s)[:1]
 except Exception as e: rec.update(status=getattr(e,'code',None),error=str(e),depth='Failure; no retry')
 rec['wall_seconds']=time.monotonic()-t; receipts.append(rec)
 print(json.dumps(rec))
wr('registry-receipts.json',json.dumps(receipts,indent=2)+'\n')
u=resource.getrusage(resource.RUSAGE_SELF)
wr('registry-job-receipt.json',json.dumps(dict(exit=0,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),wall_seconds=time.monotonic()-start,caps_before_reads=True,CPU_limit=100,AS_limit=6*1024**3,affinity=sorted(os.sched_getaffinity(0)),self_CPU_seconds=u.ru_utime+u.ru_stime,self_highwater_RSS_KiB=u.ru_maxrss,current_sample=[x for x in pathlib.Path('/proc/self/status').read_text().splitlines() if x.startswith('VmRSS:')],scope='self; not group peak',all_children_reaped=True),indent=2)+'\n')
