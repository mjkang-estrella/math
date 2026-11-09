import os,resource
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,time,datetime,sys,urllib.request,subprocess
L=pathlib.Path(__file__).resolve().parent
start=time.monotonic()
def sha(b):return hashlib.sha256(b).hexdigest()
def put(n,b):
 p=(L/n).resolve();assert p.is_relative_to(L) and p!=L
 p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b if isinstance(b,bytes) else b.encode())
def js(n,x):put(n,json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def receipt(label,extra={}):
 js('receipts/'+label+'.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),affinity=list(os.sched_getaffinity(0)),cpu_cap=120,AS_cap=6*1024**3,wall_cap=140,wall_seconds=time.monotonic()-start,self_cpu_s=resource.getrusage(resource.RUSAGE_SELF).ru_utime+resource.getrusage(resource.RUSAGE_SELF).ru_stime,self_peak_RSS_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,telemetry_scope='self high-water only; not concurrent group/cgroup peak',**extra))
r=json.loads((L/'reservation.json').read_bytes());assert sha((L/'reservation.json').read_bytes())=='0eaa4a9d2aa9e638f973b63344abab958707d4251928963cf5f666347eee29af'
if sys.argv[1]=='extract':
 ids=set(r['ids']);found={};base=L.parents[1]/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
 for p in sorted(base.glob('mathdb-normalized-chunk-*.jsonl')):
  data=p.read_bytes(); ch=sha(data)
  for i,line in enumerate(data.splitlines(keepends=True),1):
   obj=json.loads(line); ident=obj.get('id',obj.get('mathdb_id'))
   try:ident=int(ident)
   except:continue
   if ident in ids:
    assert str(ident) not in found
    put('literal/'+str(ident)+'.jsonl',line);js('parsed/'+str(ident)+'.json',obj)
    found[str(ident)]=dict(chunk=str(p),line_one_based=i,chunk_sha256=ch,raw_sha256=sha(line),statement_sha256=sha(obj.get('statement','').encode()),record=obj)
 assert len(found)==20, len(found)
 js('provenance.json',found);js('reservation-before.json',dict(sha256=sha((L/'reservation.json').read_bytes()),count=len(ids)))
 for k,v in found.items():print(k,json.dumps(v['record'],ensure_ascii=False))
 receipt('extract',dict(records=len(found)))
