import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,time,datetime,sys,re,urllib.request,urllib.error
L=pathlib.Path(__file__).resolve().parent
start=time.monotonic(); run=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%f'); reads=[]
def sha(b): return hashlib.sha256(b).hexdigest()
def write(rel,data):
 p=(L/rel).resolve(); assert p.is_relative_to(L) and p!=L
 p.parent.mkdir(parents=True,exist_ok=True)
 p.write_bytes(data if isinstance(data,bytes) else data.encode())
def js(rel,obj): write(rel,json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
def read(p):
 p=pathlib.Path(p); b=p.read_bytes(); reads.append(dict(path=str(p),bytes=len(b),sha256=sha(b))); return b
R=json.loads(read(L/'reservation.json')); assert sha((L/'reservation.json').read_bytes())=='df096d6a132ef9b8979807aa56e30b49f77b2dadace0b042508ba8acdd29dcbc'
try:
 if sys.argv[1]=='extract':
  js('reservation-before.json',dict(utc=run,sha256=sha((L/'reservation.json').read_bytes()),ids=R['ids'],count=len(R['ids'])))
  C=L.parent.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'; found={}
  for p in sorted(C.glob('mathdb-normalized-chunk-*.jsonl')):
   b=read(p); ch=sha(b)
   for n,line in enumerate(b.splitlines(keepends=True),1):
    # Text processing only, no mathematical search.
    a=json.loads(line); i=a.get('mathdb_id',a.get('id'))
    if i in R['ids']:
     assert str(i) not in found
     write(f'literals/{i}.jsonl',line); js(f'literals/{i}.json',a)
     statement=a.get('statement',''); statement=statement if isinstance(statement,str) else json.dumps(statement,ensure_ascii=False)
     found[str(i)]=dict(chunk_path=str(p),line_one_based=n,chunk_sha256=ch,raw_sha256=sha(line),raw_bytes=len(line),has_final_newline=line.endswith(b'\n'),statement_field='statement',statement_sha256=sha(statement.encode()),record=a)
  assert len(found)==20; js('provenance.json',found)
  for i,a in found.items(): print(i,json.dumps(a['record'],ensure_ascii=False))
 elif sys.argv[1]=='history':
  allow=json.loads(read(L/'historical-results-allowlist.json')); hits=[]; excluded=[]
  tokens=[str(i) for i in R['ids']]+['weakly-orient','unicentroid','tanglegram','diagram matroid','derived matroid','bidding game','triangular-grid','nonseparating planar','Vandermonde']
  for s in allow:
   if any(w in s.lower() for w in ['crown','coordinate-kernel','upper-support','reverse-kernel']): excluded.append(s); continue
   b=read(s); text=b.decode(); matches=[t for t in tokens if t.lower() in text.lower()]
   if matches:
    a=json.loads(text); hits.append(dict(path=s,matches=matches,sha256=sha(b),excerpts=[text[max(0,m.start()-150):m.end()+700] for t in matches for m in list(re.finditer(re.escape(t),text,re.I))[:3]]))
  js('historical-check.json',dict(paths_read=reads,excluded_before_open=excluded,hits=hits,limit='Only exact allowlisted completed result bodies; no recursive scan or global clearance')); print(json.dumps(hits,ensure_ascii=False)[:27000])
 elif sys.argv[1]=='fetch':
  url=sys.argv[2]; name=sys.argv[3]; utc=datetime.datetime.now(datetime.timezone.utc).isoformat(); rec=dict(url=url,utc=utc,method='GET',read_depth='acquisition only')
  try:
   req=urllib.request.Request(url,headers={'User-Agent':'Public mathematical research (bounded GET)'})
   with urllib.request.urlopen(req,timeout=30) as r:
    b=r.read(12000001); assert len(b)<=12000000
    rec.update(status=r.status,final_url=r.url,bytes=len(b),sha256=sha(b)); write('sources/'+name,b)
  except Exception as e: rec.update(error=repr(e),status=getattr(e,'code',None))
  js('receipts/http-'+run+'.json',rec); print(json.dumps(rec))
finally:
 u=resource.getrusage(resource.RUSAGE_SELF)
 js('receipts/process-'+run+'.json',dict(argv=sys.argv,utc=run,wall_seconds=time.monotonic()-start,affinity=sorted(os.sched_getaffinity(0)),CPU_limit_s=120,AS_limit_bytes=6*1024**3,self_user_system_CPU_s=u.ru_utime+u.ru_stime,self_peak_RSS_KiB=u.ru_maxrss,reads=reads,python_exception_active=sys.exc_info()[0] is not None,exit_code=1 if sys.exc_info()[0] else 0,telemetry_limit='Self high-water only, not concurrent process-group sampling',wall_timeout_external_s=140))
