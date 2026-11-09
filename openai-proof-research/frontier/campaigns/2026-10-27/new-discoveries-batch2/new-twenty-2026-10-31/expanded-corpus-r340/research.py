import os,resource
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,time,sys,urllib.request,datetime
L=pathlib.Path(__file__).resolve().parent
start=time.monotonic()
def sha(b):return hashlib.sha256(b).hexdigest()
def put(n,b):
 p=(L/n).resolve();assert p.is_relative_to(L);p.parent.mkdir(exist_ok=True,parents=True);p.write_bytes(b if isinstance(b,bytes) else b.encode())
def js(n,x):put(n,json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def receipt():
 r=resource.getrusage(resource.RUSAGE_SELF);js('resources-'+sys.argv[1]+'.json',dict(affinity=sorted(os.sched_getaffinity(0)),cpu_limit=120,AS=6*1024**3,external_wall=140,wall=time.monotonic()-start,cpu=r.ru_utime+r.ru_stime,peak_RSS_KiB=r.ru_maxrss,exit=0,children='none; process exits synchronously',limitation='self high-water only, not simultaneous process-group telemetry'))
if sys.argv[1]=='extract':
 b=(L/'reservation.json').read_bytes();assert sha(b)=='ab63294346f390bf78bcc2d397633033015ee2d02309951704733213755fef91';js('reservation-before.json',dict(sha256=sha(b),expected=(L/'reservation.sha256').read_text(),count=20))
 ids=set(json.loads(b)['ids']);out={}
 C=L.parents[1]/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
 for p in sorted(C.glob('mathdb-normalized-chunk-*.jsonl')):
  data=p.read_bytes();h=sha(data)
  for i,line in enumerate(data.splitlines(keepends=True),1):
   r=json.loads(line);id=r.get('mathdb_id',r.get('id'))
   if id in ids:
    assert id not in out;put(f'literal/{id}.jsonl',line);js(f'literal/{id}.json',r)
    out[id]=dict(chunk=str(p),line=i,chunk_sha256=h,raw_sha256=sha(line),newline=line.endswith(b'\n'),statement_sha256=sha(r.get('statement','').encode()),record=r)
 assert set(out)==ids;js('provenance.json',out)
 print(json.dumps({k:v['record'] for k,v in out.items()},ensure_ascii=False,indent=2))
 # Scalar-only shared state reading
 for name in ['ledger.json','STATUS.md']:
  p=L.parent/name
  if p.exists():
   text=p.read_text();lines=[x for x in text.splitlines() if '52' in x or '60' in x];js('scalar-'+name+'.json',dict(path=str(p),matching_count_lines=lines[:15]));print(name,lines[:8])
 allow=json.loads((L/'historical-results-allowlist.json').read_text());matches=[];inventory=[]
 for s in allow:
  if any(x in s.lower() for x in ['crown','transitive-bunkbed-formal-pi-r2']):continue
  p=pathlib.Path(s)
  if not p.is_file():continue
  data=p.read_bytes();inventory.append(dict(path=s,sha256=sha(data),bytes=len(data)))
  try:r=json.loads(data)
  except:continue
  # keep only exact ID-containing entries, avoid copying history trees
  items=list(r.values()) if isinstance(r,dict) else r
  for x in items:
   if any(str(k) in json.dumps(x) for k in ids):matches.append(dict(path=s,entry=x))
 js('history-read-inventory.json',inventory);js('history-matches.json',matches);print('HISTORY MATCHES',json.dumps(matches)[:16000])
if sys.argv[1]=='fetch':
 receipts=[]
 for url in sys.argv[2:]:
  t=datetime.datetime.now(datetime.timezone.utc).isoformat();key=sha(url.encode())[:16]
  try:
   with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research-source-reading/1.0'}),timeout=18) as f:
    b=f.read(16000000);status=f.status;final=f.url
   put('sources/'+key+'.bin',b);receipts.append(dict(url=url,utc=t,status=status,final_url=final,bytes=len(b),sha256=sha(b),file='sources/'+key+'.bin',depth='downloaded; cognitive read separately recorded'));print(url,status,len(b),key)
  except Exception as e:receipts.append(dict(url=url,utc=t,error=str(e)));print(url,str(e))
 old=L/'http-receipts.json';r=json.loads(old.read_text()) if old.exists() else [];js('http-receipts.json',r+receipts)
receipt()
