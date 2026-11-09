import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,time,datetime,sys
L=pathlib.Path(__file__).resolve().parent
start=time.monotonic()
def put(n,b):
 p=(L/n).resolve();assert p.is_relative_to(L);p.parent.mkdir(parents=True,exist_ok=True)
 if isinstance(b,str):b=b.encode()
 p.write_bytes(b)
def js(n,x):put(n,json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def sha(b):return hashlib.sha256(b).hexdigest()
res=json.loads((L/'reservation.json').read_bytes());assert sha((L/'reservation.json').read_bytes())=='9c46d764c5c8ae961a484bbbe33db4a49cf1aa9281c091a38592a77d25ce448e'
if sys.argv[1]=='extract':
 js('reservation-before.json',{'sha256':sha((L/'reservation.json').read_bytes()),'ids':res['ids'],'count':len(res['ids'])})
 corpus=L.parent.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus';found={}
 for p in sorted(corpus.glob('mathdb-normalized-chunk-*.jsonl')):
  b=p.read_bytes();h=sha(b)
  for i,line in enumerate(b.splitlines(keepends=True),1):
   r=json.loads(line);v=r.get('mathdb_id',r.get('id'))
   if v in res['ids'] or str(v) in map(str,res['ids']):
    k=str(v);put('literal/'+k+'.jsonl',line);js('literal/'+k+'.json',r)
    statement=r.get('statement',r.get('content',r.get('problem_statement','')))
    found[k]={'chunk':str(p),'line':i,'chunk_sha256':h,'raw_sha256':sha(line),'final_newline':line.endswith(b'\n'),'statement_field':next((k for k in ['statement','content','problem_statement'] if k in r),None),'statement_sha256':sha((statement if isinstance(statement,str) else json.dumps(statement,ensure_ascii=False)).encode()),'record':r}
  if len(found)==20:break
 assert len(found)==20,len(found)
 js('provenance.json',found)
 for k,v in found.items(): print(k,json.dumps(v['record'],ensure_ascii=False))
 paths=json.loads((L/'historical-results-allowlist.json').read_bytes());hist=[]
 for s in paths:
  if any(x in s.lower() for x in ['crown','state-bounds-formal-pi-r8']):continue
  p=pathlib.Path(s)
  if not p.exists():continue
  x=json.loads(p.read_bytes())
  # Only exact ID-keyed completed record matches; no recursive historical search.
  if isinstance(x,dict):
   for k in found:
    if k in x:hist.append({'path':s,'id':k,'entry':x[k]})
  elif isinstance(x,list):
   for a in x:
    if isinstance(a,dict) and str(a.get('mathdb_id',a.get('id'))) in found:hist.append({'path':s,'entry':a})
 js('history-matches.json',hist);print('HISTORY',json.dumps(hist,ensure_ascii=False))
 # Shared structured count keys only; no status prose access.
 scalars={}
 for p in [L.parent/'ledger.json',L.parent.parent/'ledger.json']:
  if p.exists():
   x=json.loads(p.read_bytes());scalars[str(p)]={k:v for k,v in x.items() if k in ['accepted_count','count','target','accepted','goal','credited_count','total_accepted'] and isinstance(v,(int,float,bool,type(None)))}
 js('shared-scalars.json',scalars)
js('process-'+sys.argv[1]+'-'+str(os.getpid())+'.json',{'pid':os.getpid(),'exit':0,'elapsed':time.monotonic()-start,'affinity':sorted(os.sched_getaffinity(0)),'cpu_limit':resource.getrlimit(resource.RLIMIT_CPU),'as_limit':resource.getrlimit(resource.RLIMIT_AS),'self_maxrss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'scope':'self only, not concurrent group peak'})
