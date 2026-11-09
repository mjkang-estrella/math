import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,sys,json,hashlib,time,subprocess,threading,urllib.request,datetime,base64
L=pathlib.Path(__file__).resolve().parent
START=time.monotonic(); RID=str(time.time_ns()); reads=[]; jobs=[]; http=[]
def sha(b): return hashlib.sha256(b).hexdigest()
def read(p):
 p=pathlib.Path(p); assert not any(s in str(p).lower() for s in ['crown','transitive-bunkbed','tournament']); b=p.read_bytes();reads.append({'path':str(p),'sha256':sha(b),'bytes':len(b),'depth':'full bytes processed; display depth separately recorded'});return b
def run(args,data=None):
 t=time.monotonic(); q=subprocess.Popen(args,stdin=subprocess.PIPE if data is not None else subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.PIPE); peak=[0]; stop=threading.Event()
 def guard():
  while not stop.is_set():
   try:
    rss=int(pathlib.Path('/proc/'+str(q.pid)+'/status').read_text().split('VmRSS:')[1].split()[0]);peak[0]=max(peak[0],rss)
    if rss>1024*1024: q.kill()
   except (FileNotFoundError,IndexError,ProcessLookupError): pass
   stop.wait(.01)
 th=threading.Thread(target=guard);th.start()
 try: out,err=q.communicate(data,timeout=125)
 except subprocess.TimeoutExpired: q.kill();out,err=q.communicate()
 finally: stop.set();th.join()
 jobs.append({'args':args,'true_exit':q.returncode,'wall_s':time.monotonic()-t,'sampled_child_peak_RSS_KiB':peak[0],'guard_limit_KiB':1024*1024,'sample_interval_s':.01,'reaped':True,'stderr':err.decode(errors='replace')})
 if q.returncode: raise RuntimeError(jobs[-1])
 return out
def write(n,data):
 if not isinstance(data,str): data=json.dumps(data,ensure_ascii=False,indent=2)+'\n'
 return run([sys.executable,'-I','-B',str(L/'write_lane.py'),n],data.encode())
def get(url,name):
 t=datetime.datetime.now(datetime.timezone.utc).isoformat();d={'url':url,'utc':t}
 try:
  op=urllib.request.build_opener(urllib.request.ProxyHandler({}))
  with op.open(urllib.request.Request(url,headers={'User-Agent':'Research-source-reader/1.0'}),timeout=35) as r:
   b=r.read(25000000);d.update(status=r.status,final_url=r.url,bytes=len(b),sha256=sha(b),content_type=r.headers.get('Content-Type'))
  write('sources/'+name+'.b64',base64.b64encode(b).decode());d['artifact']='sources/'+name+'.b64'
 except Exception as e: d['error']=str(e)
 http.append(d);return d
try:
 MODE=sys.argv[1]
 if MODE=='extract':
  rb=read(L/'reservation.json');assert sha(rb)=='b4be70501a7713288262d47cc0c9a0984e3c2869f56c583d716bbc3af8ee8ae5';print(read(L/'reservation.sha256').decode());res=json.loads(rb);ids=set(res['ids']);assert len(ids)==20
  root=L.parents[1]/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus';found={}
  for f in sorted(root.glob('mathdb-normalized-chunk-*.jsonl')):
   b=read(f);ch=sha(b)
   for i,raw in enumerate(b.splitlines(keepends=True),1):
    j=json.loads(raw); key=j.get('mathdb_id',j.get('id'))
    if key in ids:
     assert key not in found;st=j.get('statement',j.get('problem_statement',''));found[key]={'chunk_path':str(f),'chunk_sha256':ch,'one_based_line':i,'raw_sha256':sha(raw),'raw_base64':base64.b64encode(raw).decode(),'statement_utf8_sha256':sha(st.encode()),'parsed':j};write('raw/'+str(key)+'.jsonl',raw.decode());print(key,json.dumps(j,ensure_ascii=False))
  assert set(found)==ids;write('provenance.json',found);write('reservation-before.json',{'sha256':sha(rb),'ids':res['ids'],'verified':True})
 elif MODE=='history':
  allow=json.loads(read(L/'historical-results-allowlist.json')); matches=[];inv=[];ids=[str(x) for x in json.loads(read(L/'reservation.json'))['ids']]
  for p in allow:
   if any(s in p.lower() for s in ['crown','transitive-bunkbed','tournament']): continue
   b=read(p); inv.append({'path':p,'sha256':sha(b),'bytes':len(b)})
   j=json.loads(b)
   def walk(x):
    if isinstance(x,dict):
     if any(str(x.get(k,'')) in ids for k in ['mathdb_id','id']): matches.append({'path':p,'entry':x})
     else:
      for k,v in x.items():
       if k in ids: matches.append({'path':p,'entry':v})
       else: walk(v)
    elif isinstance(x,list):
     for y in x: walk(y)
   walk(j)
  write('history-inventory.json',inv);write('history-matches.json',matches);print(json.dumps(matches,ensure_ascii=False))
 elif MODE=='fetch':
  for spec in sys.argv[2:]:
   name,url=spec.split('=',1);print(json.dumps(get(url,name)))
 elif MODE=='text':
  for name in sys.argv[2:]:
   b=base64.b64decode(read(L/('sources/'+name+'.b64')))
   if b.startswith(b'%PDF'):
    # PDF passed over stdin; no uncontrolled temporary writes.
    out=run(['pdftotext','-layout','-','-'],b);write('sources/'+name+'.txt',out.decode(errors='replace'));print(name,'characters',len(out))
   else: print(name,b.decode(errors='replace')[:2000])
 elif MODE=='read':
  for spec in sys.argv[2:]:
   n,a,z=spec.rsplit(':',2);lines=read(L/n).decode().splitlines();print('FILE',n,'TOTAL',len(lines));print('\n'.join(f'{i+1}: {x}' for i,x in enumerate(lines) if int(a)<=i+1<=int(z)))
finally:
 u=resource.getrusage(resource.RUSAGE_SELF)
 receipt={'run_id':RID,'mode':sys.argv[1:],'reads':reads,'jobs':jobs,'http':http,'wall_s':time.monotonic()-START,'affinity':sorted(os.sched_getaffinity(0)),'CPU_limit_s':120,'AS_limit_bytes':6*1024**3,'external_wall_limit_s':140,'self_peak_RSS_KiB':u.ru_maxrss,'CPU_s':u.ru_utime+u.ru_stime,'limits':'10ms child RSS samples, not transient/group/cgroup maxima; no mathematical execution'}
 write('receipts/'+RID+'.json',receipt)
