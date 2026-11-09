import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,time,datetime,sys,re,urllib.request,urllib.error,subprocess
L=pathlib.Path(__file__).resolve().parent
start=time.monotonic()
def sha(b):return hashlib.sha256(b).hexdigest()
def put(n,b):
 p=(L/n).resolve(); assert p.is_relative_to(L) and p!=L
 p.parent.mkdir(parents=True,exist_ok=True); p.write_bytes(b if isinstance(b,bytes) else b.encode())
def js(n,v):put(n,json.dumps(v,ensure_ascii=False,indent=2)+'\n')
def receipt(name,extra={}):
 u=resource.getrusage(resource.RUSAGE_SELF);js('receipts/'+name+'.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),affinity=sorted(os.sched_getaffinity(0)),cpu_limit=120,as_limit=6*1024**3,wall_limit=140,wall_s=time.monotonic()-start,self_cpu_s=u.ru_utime+u.ru_stime,self_peak_rss_kib=u.ru_maxrss,telemetry='self high water, not concurrent process-group peak',**extra))
mode=sys.argv[1]
if mode=='extract':
 b=(L/'reservation.json').read_bytes(); assert sha(b)=='f6fb492244c6645afe8b39029511ca8cc3b08d11898a5d9f7e626802eb1c041c';r=json.loads(b);ids=set(r['ids']);assert len(ids)==20
 js('reservation-before.json',{'sha256':sha(b),'ids':r['ids'],'verified':True})
 C=L.parents[1]/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
 out={}
 for p in sorted(C.glob('mathdb-normalized-chunk-*.jsonl')):
  data=p.read_bytes(); ch=sha(data)
  for i,line in enumerate(data.splitlines(keepends=True),1):
   rec=json.loads(line); mid=rec.get('mathdb_id',rec.get('id'))
   if mid in ids:
    assert str(mid) not in out;put(f'literal/{mid}.jsonl',line);js(f'literal/{mid}.json',rec)
    statement=rec.get('statement',rec.get('statement_text',''));out[str(mid)]={'chunk':str(p),'line_1based':i,'chunk_sha256':ch,'raw_sha256':sha(line),'statement_sha256':sha(statement.encode()),'raw_newline':line.endswith(b'\n'),'record':rec}
 assert len(out)==20;js('provenance.json',out)
 for k,v in out.items(): print(k,json.dumps(v['record'],ensure_ascii=False))
 # Only allowlisted completed exact result files; filter protected names before opening.
 terms=[str(i) for i in ids]+[x['source_url'].split('/')[-1] for x in r['rows']]+['quasi-dihedral','subtraction game','Li–Qu','Carnevale','spectral partition','Sokal','skew-symmetric plane','multi-away','shifted Young','matroidal']
 history=[];inventory=[]
 for s in json.loads((L/'historical-results-allowlist.json').read_text()):
  if any(t in s.lower() for t in ['crown','state-bounds','coordinate-map','coordinate-kernel']):continue
  p=pathlib.Path(s)
  if not p.is_file(): inventory.append({'path':s,'status':'missing'});continue
  b=p.read_bytes();inventory.append({'path':s,'bytes':len(b),'sha256':sha(b)})
  obj=json.loads(b)
  def walk(x):
   if isinstance(x,dict):
    if any(t.lower() in json.dumps(x,ensure_ascii=False).lower() for t in terms):
     if any(isinstance(v,(dict,list)) for v in x.values()):
      for v in x.values():walk(v)
     else:history.append({'path':s,'entry':x})
   elif isinstance(x,list):
    for v in x:walk(v)
  walk(obj)
 js('history-inventory.json',inventory);js('history-matches.json',history);print('HISTORY',json.dumps(history,ensure_ascii=False)[:14000])
 # shared scalar only; no full copies
 scalars={}
 for p in [L.parent/'ledger.json',L.parent/'STATUS.md',L.parents[1]/'ledger.json',L.parents[1]/'prior-campaign-context.json']:
  if p.exists():
   text=p.read_text();scalars[str(p)]={'scalar_lines':[s for s in text.splitlines() if re.search(r'52/60|"(?:accepted_count|target|count|accepted_total)"\s*:\s*\d+',s)][:12]}
 js('shared-scalars.json',scalars)
 receipt('extract',{'outcome':'20 literal records bound; allowlisted history only','true_exit':0})
elif mode=='fetch':
 name,url=sys.argv[2:4];t=time.monotonic();info={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'method':'GET'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'ordinary-math-source-review/1.0'}),timeout=35) as q:
   b=q.read(16000001);assert len(b)<=16000000
   info.update(status=q.status,final_url=q.url,bytes=len(b),sha256=sha(b),content_type=q.headers.get('Content-Type'));put('sources/'+name,b)
 except Exception as e:info.update(error=repr(e),status=getattr(e,'code',None))
 info['duration_s']=time.monotonic()-t;js('http/'+name+'.json',info);print(json.dumps(info));receipt('fetch-'+name,{'true_exit':0,'outcome':'access result recorded; errors are not clearance'})
elif mode=='read':
 p=L/sys.argv[2];s=p.read_text(errors='replace');a=int(sys.argv[3]);b=int(sys.argv[4]);lines=s.splitlines();print('\n'.join(f'{i+1}: {lines[i]}' for i in range(a-1,min(b,len(lines)))));receipt('read-'+p.stem+'-'+str(a)+'-'+str(b),{'true_exit':0,'path':str(p),'lines':[a,min(b,len(lines))]})
