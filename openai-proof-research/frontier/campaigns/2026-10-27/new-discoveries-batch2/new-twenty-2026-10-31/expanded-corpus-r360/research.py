import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,time,datetime,re,sys,urllib.request,urllib.error,concurrent.futures
L=pathlib.Path(__file__).resolve().parent
H=lambda b:hashlib.sha256(b).hexdigest()
def write(n,b):
 p=(L/n).resolve(); assert p.is_relative_to(L); p.parent.mkdir(exist_ok=True,parents=True); p.write_bytes(b if isinstance(b,bytes) else b.encode())
def dump(n,x):write(n,json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def receipt(n,extra={}):dump('receipts/'+n+'-'+str(time.time_ns())+'.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),affinity=sorted(os.sched_getaffinity(0)),cpu_limit=resource.getrlimit(resource.RLIMIT_CPU),as_limit=resource.getrlimit(resource.RLIMIT_AS),self_rusage=list(resource.getrusage(resource.RUSAGE_SELF)),exit=0,**extra))
r=json.loads((L/'reservation.json').read_bytes()); assert H((L/'reservation.json').read_bytes())=='18bb899148b2e2f04a36acb0a8c1ef36e62d617d4e6779da2cf2bee6ad4d12fc'; assert len(set(r['ids']))==20
if sys.argv[1]=='extract':
 found={}; C=L.parents[1]/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
 for p in sorted(C.glob('mathdb-normalized-chunk-*.jsonl')):
  b=p.read_bytes(); ch=H(b)
  for k,line in enumerate(b.splitlines(keepends=True),1):
   d=json.loads(line); ident=d.get('id',d.get('mathdb_id'))
   if ident in r['ids']:
    assert str(ident) not in found
    write('literal/'+str(ident)+'.jsonl',line); dump('literal/'+str(ident)+'.json',d)
    stmt=d.get('statement',d.get('content',d.get('problem_statement','')))
    found[str(ident)]=dict(chunk=str(p),line=k,chunk_sha256=ch,raw_sha256=H(line),statement_sha256=H(stmt.encode()),statement_field='statement',record=d)
 dump('provenance.json',found); print('FOUND',len(found)); assert len(found)==20
 for i,d in found.items(): print(i,json.dumps(d['record'],ensure_ascii=False))
 receipt('extract',{'reservation_sha256':H((L/'reservation.json').read_bytes())})
if sys.argv[1]=='history':
 out=[]; terms=[str(i) for i in r['ids']]+['021-avoid','non-evasive','semicomplete','Grothendieck','Rayleigh','Toroczkai','CMPP','Gabow','Backman','rotational sequenc']
 for s in json.loads((L/'historical-results-allowlist.json').read_text()):
  if any(t in s.lower() for t in ['crown','kernel','upper-support','upper-suppor']):continue
  p=pathlib.Path(s)
  try:b=p.read_bytes()
  except FileNotFoundError:continue
  txt=b.decode(); matches=[t for t in terms if t.lower() in txt.lower()]
  out.append(dict(path=s,sha256=H(b),bytes=len(b),matches=matches))
  if matches:print(s, matches); print(txt[:16000] if len(txt)<16000 else '\n'.join(line for line in txt.splitlines() if any(t.lower() in line.lower() for t in matches))[:18000])
 dump('history-check.json',out); receipt('history')
if sys.argv[1]=='fetch':
 jobs=json.loads((L/sys.argv[2]).read_text())
 def fetch(job):
  name,url=job; t=time.time(); rec=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),method='GET',read_depth='acquired_not_yet_read')
  try:
   with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source review (public GET)'}),timeout=22) as f:
    b=f.read(12000000);rec.update(status=f.status,final_url=f.url,bytes=len(b),sha256=H(b));write('sources/'+name,b)
  except Exception as e:rec.update(error=str(e),status=getattr(e,'code',None))
  rec['wall_s']=time.time()-t;dump('http/'+name+'.json',rec);print(name,rec)
 with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:list(ex.map(fetch,jobs))
 receipt('fetch',{'all_threads_joined':True})
