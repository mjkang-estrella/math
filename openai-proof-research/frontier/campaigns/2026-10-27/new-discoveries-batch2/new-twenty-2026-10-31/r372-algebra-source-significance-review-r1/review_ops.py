import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,sys,json,time,hashlib,subprocess,select
LANE=pathlib.Path(__file__).resolve().parent
BASE=LANE.parent/'expanded-corpus-r372'
reads=[]
def read(p):
 p=pathlib.Path(p).resolve(); assert p.is_relative_to(BASE) or p.is_relative_to(LANE) or p.name in ('AGENTS.md','ledger.json','prior-campaign-context.json','upstream.json','CONTENTS.md','expanded-corpus-r372-parent-integration.json')
 assert not any(s in str(p).lower() for s in ('crown','bunkbed','tournament'))
 t=time.time(); b=p.read_bytes(); reads.append(dict(path=str(p),utc_epoch=t,bytes=len(b),sha256=hashlib.sha256(b).hexdigest())); return b

def write(name,body):
 start=time.time(); p=subprocess.Popen([sys.executable,'-I','-B',str(LANE/'write_lane.py'),name],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE); p.stdin.write(body.encode()); p.stdin.close(); peak=0; samples=0
 while p.poll() is None:
  try:
   status=pathlib.Path('/proc')/str(p.pid)/'status'; txt=status.read_text(); rss=int(next(x.split()[1] for x in txt.splitlines() if x.startswith('VmRSS:')))*1024; peak=max(peak,rss);samples+=1
   if rss>512*1024**2: p.kill()
  except (FileNotFoundError,StopIteration): pass
  time.sleep(.002)
 out=p.stdout.read().decode(); err=p.stderr.read().decode(); rc=p.wait(); assert rc==0,(rc,err)
 return dict(name=name,start=start,end=time.time(),returncode=rc,child_peak_sampled_rss=peak,samples=samples,stdout=out)

def finish(tag):
 r=dict(tag=tag,reads=reads,finished=time.time(),self_usage=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,affinity=sorted(os.sched_getaffinity(0)),cpu_limit=resource.getrlimit(resource.RLIMIT_CPU),as_limit=resource.getrlimit(resource.RLIMIT_AS),exit_intent=0)
 print(json.dumps(write('receipt-'+tag+'.json',json.dumps(r,indent=2))))
if __name__=='__main__':
 tag=sys.argv[1]
 if tag=='inventory':
  print(read(LANE/'frozen-inputs.json').decode())
  for n in ('BRIEF.md','DERIVATIONS.md','results.json','provenance.json'):
   p=BASE/n
   if p.exists(): print('\nFILE '+str(p)+'\n'+read(p).decode())
 elif tag=='read':
  for s in sys.argv[2:]: print('\nFILE '+s+'\n'+read(s).decode())
 finish(tag+'-'+str(time.time_ns()))
