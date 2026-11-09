import os,sys,subprocess,time,resource,json,pathlib,signal
W=pathlib.Path(__file__).resolve().parent
os.environ.update(MALLOC_ARENA_MAX='2',TMPDIR=str(W),PYTHONDONTWRITEBYTECODE='1')
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120))
name=sys.argv[1];start=time.monotonic()
p=subprocess.Popen(sys.argv[2:],cwd=W,stdout=open(W/(name+'.log'),'w'),stderr=subprocess.STDOUT,start_new_session=True)
peak=0;reason=None
while p.poll() is None:
 try:
  vals=dict((a.strip(),int(b.split()[0])) for a,b in (s.split(':',1) for s in pathlib.Path('/proc/'+str(p.pid)+'/smaps_rollup').read_text().splitlines() if ':' in s) if b.strip().split()[0].isdigit())
  peak=max(peak,sum(vals.get(x,0) for x in ['Private_Clean','Private_Dirty','Private_Hugetlb']))
 except (OSError,ValueError): pass
 if peak>6*1024*1024 or time.monotonic()-start>140:
  reason='RSS or wall cap';os.killpg(p.pid,signal.SIGKILL);break
 time.sleep(.1)
p.wait();result=dict(command=sys.argv[2:],returncode=p.returncode,seconds=time.monotonic()-start,peak_private_KiB=peak,killed=reason)
(W/(name+'.receipt.json')).write_text(json.dumps(result,indent=2));print(result);sys.exit(p.returncode)
