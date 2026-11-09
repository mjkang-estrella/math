import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,time,datetime,sys,atexit
L=pathlib.Path(__file__).resolve().parent
start=time.monotonic()
def sha(b):return hashlib.sha256(b).hexdigest()
def write(n,b):
 p=(L/n).resolve();assert p.is_relative_to(L) and not p.is_symlink();p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b if isinstance(b,bytes) else b.encode())
def js(n,o):write(n,json.dumps(o,indent=2,ensure_ascii=False)+'\n')
def receipt():
 r=resource.getrusage(resource.RUSAGE_SELF);o={'argv':sys.argv,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'wall_s':time.monotonic()-start,'affinity':sorted(os.sched_getaffinity(0)),'CPU_limit_s':120,'AS_limit_bytes':6*1024**3,'self_CPU_s':r.ru_utime+r.ru_stime,'self_highwater_RSS_KiB':r.ru_maxrss,'current_VmRSS':[s for s in pathlib.Path('/proc/self/status').read_text().splitlines() if s.startswith('VmRSS:')],'children':'none; fetch threads joined if used','telemetry_limit':'not group/cgroup/transient sampling','true_exit':'external exec receipt is authoritative'};js('receipts/'+str(time.time_ns())+'.json',o)
atexit.register(receipt)
assert sha((L/'reservation.json').read_bytes())=='55699bf7706b976f6e46e55da5904608d868bf20412fb305bda4f39e4612bd6a'
R=json.loads((L/'reservation.json').read_text());ids=set(R['ids'])
if sys.argv[1]=='extract':
 root=L.parents[1]/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
 found={}
 for p in sorted(root.glob('mathdb-normalized-chunk-*.jsonl')):
  b=p.read_bytes();h=sha(b)
  for i,line in enumerate(b.splitlines(keepends=True),1):
   o=json.loads(line);v=o.get('mathdb_id',o.get('id'))
   if v in ids:
    assert str(v) not in found
    write('raw/'+str(v)+'.jsonl',line)
    found[str(v)]={'chunk':str(p),'chunk_sha256':h,'onebasedline':i,'raw_sha256':sha(line),'newline_hex':line[-1:].hex(),'fullparsedJSON':o}
 assert len(found)==20
 js('literal-records.json',found)
 print('KEYS',next(iter(found.values()))['fullparsedJSON'].keys())
 print('ALL20 full parsed JSON:')
 for k,v in found.items():print(k,json.dumps(v['fullparsedJSON'],ensure_ascii=False))
elif sys.argv[1]=='history':
 allow=json.loads((L/'historical-results-allowlist.json').read_text());out=[]
 for s in allow:
  if any(t in s.lower() for t in ['crown','transitive-bunkbed','tournament','protected']):continue
  p=pathlib.Path(s);b=p.read_bytes();o=json.loads(b)
  # Only exact completed allowlisted result artifacts; report matching ID/title/source, not unrelated bodies.
  rows=o if isinstance(o,list) else list(o.values()) if isinstance(o,dict) else []
  matches=[x for x in rows if any(str(i) in json.dumps(x) for i in ids) or any(r['source_url'] in json.dumps(x) for r in R['rows'])]
  out.append({'path':s,'sha256':sha(b),'matching_rows':matches})
 js('history-reconciliation.json',out);print('completed exact artifacts',len(out));print(json.dumps([x for x in out if x['matching_rows']],ensure_ascii=False))
