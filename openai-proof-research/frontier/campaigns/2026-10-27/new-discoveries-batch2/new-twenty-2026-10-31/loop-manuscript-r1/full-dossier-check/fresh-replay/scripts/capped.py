#!/usr/bin/env python3
"""Independent strict replay. Run only in a fresh extraction; no shared writes."""
import os,sys,pathlib,subprocess,resource,time,signal,json,hashlib,re,uuid
D=pathlib.Path(__file__).resolve().parents[1]
B=pathlib.Path('/usr/bin'); P=D/'unused-packages'
F=D; L=D/'receipts'; L.mkdir(exist_ok=True)

env={**os.environ,'PATH':str(B)+':'+os.environ.get('PATH','/usr/bin:/bin'),'LEAN_PATH':str(F)+':'+':'.join(str(p) for p in sorted(P.glob('*/.lake/build/lib/lean'))),'MALLOC_ARENA_MAX':'2','OMP_NUM_THREADS':'1','OPENBLAS_NUM_THREADS':'1'}
receipts=[]; made=[]
def run(tag,cmd,ok=True):
 def pre():
  os.setsid();os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(64*1024**3,64*1024**3))
 # Use a user scope if available; it is supplementary to process-tree sampling.
 unit='mathdb380362-'+uuid.uuid4().hex
 probe=subprocess.run(['systemd-run','--user','--scope','--quiet','-p','MemoryMax=6G','true'],capture_output=True,timeout=10)
 scope=probe.returncode==0
 actual=(['systemd-run','--user','--scope','--quiet','--unit='+unit,'-p','MemoryMax=6G'] if scope else [])+cmd
 t=time.monotonic();peak=private=0;reason=None
 with (L/(tag+'.log')).open('w') as log:
  p=subprocess.Popen(actual,cwd=F,env=env,stdout=log,stderr=subprocess.STDOUT,preexec_fn=pre)
  while p.poll() is None:
   total=priv=0
   for q in pathlib.Path('/proc').glob('[0-9]*'):
    try:
     if os.getpgid(int(q.name))!=p.pid:continue
     s=(q/'status').read_text();total+=int(re.search(r'VmRSS:\s+(\d+)',s)[1])*1024
     sm=(q/'smaps_rollup').read_text();priv+=sum(int(v) for v in re.findall(r'^Private_(?:Clean|Dirty|Hugetlb):\s+(\d+)',sm,re.M))*1024
    except (OSError,TypeError,ProcessLookupError):pass
   peak=max(peak,total);private=max(private,priv)
   if priv>6*1024**3 or time.monotonic()-t>140:
    reason='private RSS or wall limit';os.killpg(p.pid,signal.SIGKILL);break
   time.sleep(.1)
  p.wait()
 r=dict(tag=tag,command=cmd,returncode=p.returncode,wall_seconds=time.monotonic()-t,cpu_limit_seconds=120,wall_limit_seconds=140,AS_limit_bytes=64*1024**3,private_RSS_limit_bytes=6*1024**3,cpus=sorted(os.sched_getaffinity(0))[:2],sample_seconds=0.1,total_VmRSS_peak=peak,private_RSS_peak=private,MemoryMax_6G=scope,scope_probe_error=probe.stderr.decode(),cap_reason=reason)
 receipts.append(r);(L/(tag+'.json')).write_text(json.dumps(r,indent=2)+'\n');print(tag,p.returncode,round(r['wall_seconds'],2),flush=True)
 assert reason is None, r
 if ok:assert p.returncode==0,(tag,(L/(tag+'.log')).read_text()[-5000:])
 else:assert p.returncode!=0 and 'error:' in (L/(tag+'.log')).read_text()
 return (L/(tag+'.log')).read_text()


run(sys.argv[1],sys.argv[2:])
