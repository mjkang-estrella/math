import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,time,sys,subprocess
lane=pathlib.Path(__file__).resolve().parent
start=time.time(); reads=[]
def write(n,s):
 p=subprocess.Popen([sys.executable,'-I','-B',str(lane/'write_lane.py'),n],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
 p.stdin.write(s);p.stdin.close(); samples=[]
 while p.poll() is None:
  try:
   status=pathlib.Path('/proc/%s/status'%p.pid).read_text(); rss=next((int(x.split()[1]) for x in status.splitlines() if x.startswith('VmRSS:')),0);samples.append({'UTC_epoch':time.time(),'pid':p.pid,'RSS_KiB':rss})
   if rss>6*1024**2:p.kill()
  except FileNotFoundError:pass
  time.sleep(.005)
 out=p.stdout.read();err=p.stderr.read(); rc=p.wait();print('WRITE',n,rc,out,err)
 return {'path':n,'pid':p.pid,'exit':rc,'samples':samples,'reaped':True,'descendants':'writer starts no children'}
def read(p):
 p=pathlib.Path(p).resolve(); assert not any(x in str(p).lower() for x in ['crown','bunkbed','tournament']);b=p.read_bytes();reads.append({'path':str(p),'UTC_epoch':time.time(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()});return b.decode()
mode=sys.argv[1]
try:
 if mode=='windows':
  for f,lo,hi in zip(sys.argv[2::3],sys.argv[3::3],sys.argv[4::3]):
   lines=read(f).splitlines();print('FILE',f,'LINES',lo,hi);print('\n'.join(str(i+1)+': '+v for i,v in enumerate(lines) if int(lo)<=i+1<=int(hi)))
 elif mode=='agents':
  for d in reversed([lane,*lane.parents]):
   f=d/'AGENTS.md'
   if f.is_file(): print('FILE',f,read(f))
 elif mode=='file':
  for f in sys.argv[2:]: print('FILE',f,read(f))
 elif mode=='selected':
  root=lane.parent/'expanded-corpus-r375'
  for n in ['results.json','raw-provenance.json']:
   a=json.loads(read(root/n)); print('STRUCTURE',n,type(a).__name__)
   if isinstance(a,dict):
    print('KEYS',list(a));print(json.dumps(a.get('323739',a if len(a)<5 else None),indent=2))
   else:print(json.dumps([v for v in a if '323739' in str(v)],indent=2))
finally:
 u=resource.getrusage(resource.RUSAGE_SELF);r={'start':start,'end':time.time(),'reads':reads,'affinity':sorted(os.sched_getaffinity(0)),'CPU_limit':120,'AS_limit':6*1024**3,'self_peak_RSS_KiB':u.ru_maxrss,'CPU_s':u.ru_utime+u.ru_stime,'reader_children':'only receipt writer; no converters','body_exception':sys.exc_info()[0] is not None}
 w=write('receipt-'+str(time.time_ns())+'.json',json.dumps(r,indent=2));print('WRITER_GUARD',json.dumps(w))
