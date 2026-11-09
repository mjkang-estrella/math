import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,sys,json,time,datetime,traceback
L=pathlib.Path(__file__).resolve().parent
start=time.monotonic(); code=0
name=sys.argv[1]; assert name.replace('_','').isalnum()
def put(n,b):
 p=(L/n).resolve(); assert p.is_relative_to(L) and p!=L and not p.is_symlink();p.parent.mkdir(parents=True,exist_ok=True)
 if isinstance(b,bytes):p.write_bytes(b)
 else:p.write_text(b)
def dump(n,x):put(n,json.dumps(x,indent=2,ensure_ascii=False)+'\n')
try:exec(compile(sys.stdin.read(),'<'+name+'>','exec'))
except BaseException as e:
 code=e.code if isinstance(e,SystemExit) and isinstance(e.code,int) else 1;traceback.print_exc()
finally:
 r=resource.getrusage(resource.RUSAGE_SELF)
 dump('receipts/'+name+'.json',dict(exit=code,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),affinity=sorted(os.sched_getaffinity(0)),cpu_cap=120,as_cap=6*1024**3,external_wall_cap=140,wall=time.monotonic()-start,self_cpu=r.ru_utime+r.ru_stime,self_peak_rss_KiB=r.ru_maxrss,telemetry_scope='self only; no concurrent group/cgroup measurement',children='none unless explicitly recorded'))
sys.exit(code)
