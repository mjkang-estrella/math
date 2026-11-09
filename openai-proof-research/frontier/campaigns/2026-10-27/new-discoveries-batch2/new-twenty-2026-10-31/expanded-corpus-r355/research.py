import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,time,datetime,sys,atexit
P=pathlib.Path(__file__).resolve().parent
start=time.monotonic()
def put(rel,data):
 p=(P/rel).resolve(); assert p.is_relative_to(P); p.parent.mkdir(parents=True,exist_ok=True); p.write_bytes(data if isinstance(data,bytes) else data.encode())
def js(rel,obj): put(rel,json.dumps(obj,ensure_ascii=False,indent=2)+'\n')
def sha(b): return hashlib.sha256(b).hexdigest()
def receipt():
 js('process-'+sys.argv[1]+'-'+str(os.getpid())+'.json',dict(pid=os.getpid(),mode=sys.argv[1],utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),wall=time.monotonic()-start,affinity=list(os.sched_getaffinity(0)),rusage=list(resource.getrusage(resource.RUSAGE_SELF)),note='self telemetry only; outer shell reports actual exit; no group peak claimed'))
atexit.register(receipt)
r=json.loads((P/'reservation.json').read_bytes()); ids=set(r['ids']); assert len(ids)==20 and sha((P/'reservation.json').read_bytes())=='ff5b598a3d7bf11c8fef0336ea5e75de16f1d564ae5bff8c72ab2d59df1e0713'
if sys.argv[1]=='extract':
 js('reservation-before.json',dict(sha256=sha((P/'reservation.json').read_bytes()),ids=r['ids']))
 corpus=P.parents[1]/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
 out={}
 for p in sorted(corpus.glob('mathdb-normalized-chunk-*.jsonl')):
  data=p.read_bytes(); ch=sha(data)
  for n,line in enumerate(data.splitlines(keepends=True),1):
   # corpus binding only; no mathematical enumeration
   rec=json.loads(line); i=rec.get('mathdb_id',rec.get('id'))
   if i in ids:
    assert str(i) not in out and line.endswith(b'\n'); put('literal/'+str(i)+'.jsonl',line)
    statement=rec.get('statement',rec.get('content',rec.get('body','')))
    out[str(i)]=dict(chunk=str(p),line=n,chunk_sha256=ch,raw_sha256=sha(line),statement_sha256=sha(statement.encode()),statement_field='statement' if 'statement' in rec else 'content' if 'content' in rec else 'body',record=rec)
 assert len(out)==20; js('provenance.json',out)
 for i in r['ids']: print(i,json.dumps(out[str(i)]['record'],ensure_ascii=False))
