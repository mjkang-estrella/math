import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,sys,time,datetime,traceback,urllib.request,urllib.error,concurrent.futures,html.parser,re
P=pathlib.Path(__file__).resolve().parent; started=time.monotonic(); token=str(time.time_ns()); reads=[]; accesses=[]
def sha(b): return hashlib.sha256(b).hexdigest()
def write(n,b):
 p=(P/n).resolve(); assert p.is_relative_to(P); p.parent.mkdir(parents=True,exist_ok=True); p.write_bytes(b if isinstance(b,bytes) else b.encode())
def save(n,x): write(n,json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def read(p):
 p=pathlib.Path(p); assert 'crown' not in str(p).lower() and 'transitive-bunkbed-prefix-helpers-formal' not in str(p)
 b=p.read_bytes(); reads.append({'path':str(p),'bytes':len(b),'sha256':sha(b)}); return b
class Parser(html.parser.HTMLParser):
 def __init__(self): super().__init__(); self.parts=[]; self.skip=0
 def handle_starttag(self,t,a):
  if t in ('script','style'): self.skip+=1
  d=dict(a)
  if t=='img' and d.get('alt'): self.parts.append(d['alt'])
 def handle_endtag(self,t):
  if t in ('script','style'): self.skip=max(0,self.skip-1)
  if t in ('p','div','section','h1','h2','h3','h4','tr'): self.parts.append('\n')
 def handle_data(self,d):
  if not self.skip:self.parts.append(d)
def fetch(pair):
 name,url=pair; rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'method':'GET','read_depth':'acquired only'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'source-research/1.0'}),timeout=32) as r:
   b=r.read(24000000); rec.update(status=r.status,final_url=r.url,bytes=len(b),sha256=sha(b),headers=dict(r.headers)); write('sources/'+name,b)
  if b.lstrip().startswith(b'<'):
   parser=Parser();parser.feed(b.decode('utf-8',errors='replace'));write('sources/'+name+'.txt',''.join(parser.parts))
 except Exception as e: rec.update(error=str(e),status=getattr(e,'code',None))
 accesses.append(rec);return {'name':name,**rec}
def main():
 mode=sys.argv[1]
 if mode=='init':
  r=json.loads(read(P/'reservation.json')); assert sha((P/'reservation.json').read_bytes())=='473cc74dc92b396733b2bd249d09e270f4ecf921679204dba29dcce83fdd4470'; ids=set(r['ids']); out={}
  corpus=P.parents[1]/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
  for path in sorted(corpus.glob('mathdb-normalized-chunk-*.jsonl')):
   b=read(path); ch=sha(b)
   for ln,raw in enumerate(b.splitlines(keepends=True),1):
    obj=json.loads(raw); i=obj.get('id',obj.get('mathdb_id'))
    if i is not None and int(i) in ids:
     i=str(i); write('literal/'+i+'.jsonl',raw);save('literal/'+i+'.json',obj); st=obj.get('statement',''); out[i]={'chunk':str(path),'line_one_based':ln,'chunk_sha256':ch,'raw_sha256':sha(raw),'raw_final_newline':raw.endswith(b'\n'),'statement_sha256':sha(st.encode()),'record':obj}; print(i,json.dumps(obj,ensure_ascii=False))
  assert set(map(int,out))==ids;save('provenance.json',out)
  hist=[]
  for path in json.loads(read(P/'historical-results-allowlist.json')):
   if 'crown' in path.lower() or 'transitive-bunkbed-prefix-helpers-formal' in path: continue
   pp=pathlib.Path(path)
   if not pp.is_file():continue
   b=read(pp); text=b.decode(errors='replace'); matched=[str(i) for i in ids if str(i) in text]; families=[s for s in ['Roberson','coarse separator','Hadamard pair','reverse oddtown','Speyer','Gaussian-polynomial','tree-independence'] if s.lower() in text.lower()]
   if matched or families: hist.append({'path':path,'sha256':sha(b),'ids':matched,'families':families,'body':json.loads(b)})
  save('history-matches.json',hist); print('HISTORY',[(x['path'].split('/')[-2],x['ids'],x['families']) for x in hist])
  for base in [P.parent,P.parents[1]]:
   for n in ['ledger.json','STATUS.md']:
    f=base/n
    if f.is_file():
     b=read(f)
     if n.endswith('json'):
      obj=json.loads(b); print('SCALARS',str(f),{k:v for k,v in obj.items() if k in ['accepted_new','target']})
     else: print('SCALARS STATUS read; no lines dumped')
  for f in [P.parents[4]/'sources/upstream.json',P.parents[4]/'sources/CONTENTS.md']:
   if f.is_file(): read(f)
 elif mode=='fetch':
  pairs=json.loads(read(P/sys.argv[2]));
  with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
   for result in pool.map(fetch,pairs): print(json.dumps({k:v for k,v in result.items() if k!='headers'}))
 elif mode=='read':
  for name in sys.argv[2:]:
   b=read(P/name);print('FILE',name); print(b.decode(errors='replace'))
 else: raise ValueError(mode)
code=0
try: main()
except BaseException: code=1;traceback.print_exc()
finally:
 u=resource.getrusage(resource.RUSAGE_SELF);save('receipts/process-'+token+'.json',{'argv':sys.argv,'true_python_exit':code,'wall_seconds':time.monotonic()-started,'affinity':sorted(os.sched_getaffinity(0)),'CPU_limit':120,'AS_limit':6*1024**3,'external_wall_limit':140,'self_cpu':u.ru_utime+u.ru_stime,'self_peak_RSS_KiB':u.ru_maxrss,'telemetry_limit':'self peak only, no concurrent group measurement; threads joined','reads':reads,'http':accesses})
sys.exit(code)
