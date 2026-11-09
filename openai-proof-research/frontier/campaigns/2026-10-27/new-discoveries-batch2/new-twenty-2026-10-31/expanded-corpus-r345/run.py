import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,time,sys,uuid,datetime,traceback,urllib.request,urllib.error
P=pathlib.Path(__file__).resolve().parent
start=time.monotonic(); tag=str(uuid.uuid4()); reads=[]; accesses=[]
def write(n,data):
 p=(P/n).resolve(); assert p.is_relative_to(P)
 p.parent.mkdir(parents=True,exist_ok=True)
 p.write_bytes(data if isinstance(data,bytes) else data.encode())
def save(n,obj): write(n,json.dumps(obj,ensure_ascii=False,indent=2)+"\n")
def read(p):
 p=pathlib.Path(p).resolve(); assert not any(x in str(p).lower() for x in ['crown-cut','crown-vnumber','transitive-bunkbed-reach-bridge-formal-pi-r4'])
 b=p.read_bytes(); reads.append({'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}); return b

def fetch(url,name):
 t=datetime.datetime.now(datetime.timezone.utc).isoformat(); receipt={'url':url,'utc':t,'method':'GET','read_depth':'acquired only'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-review/1.0'}),timeout=25) as r:
   b=r.read(16000000); receipt.update(status=r.status,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),final_url=r.url); write(name,b)
 except Exception as e: receipt.update(error=str(e),status=getattr(e,'code',None))
 accesses.append(receipt); return receipt
code=sys.stdin.read(); ec=0
try: exec(compile(code,'lane-operation','exec'))
except BaseException:
 ec=1; traceback.print_exc()
finally:
 save('receipts/'+tag+'.json',{'exit':ec,'affinity':sorted(os.sched_getaffinity(0)),'CPU_limit_s':120,'AS_limit_bytes':6*1024**3,'wall_limit_s':140,'elapsed':time.monotonic()-start,'self_usage':list(resource.getrusage(resource.RUSAGE_SELF)),'telemetry_limit':'self high water only; no concurrent group peak; no children launched','reads':reads,'accesses':accesses})
sys.exit(ec)
