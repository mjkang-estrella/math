import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,time,sys,subprocess,urllib.request,base64
lane=pathlib.Path(__file__).resolve().parent;root=lane.parent/'expanded-corpus-r375';start=time.time();reads=[];writes=[];access=[]
def write(n,s):
 p=subprocess.Popen([sys.executable,'-I','-B',str(lane/'write_lane.py'),n],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True);p.stdin.write(s);p.stdin.close();samples=[]
 while p.poll() is None:
  try:
   st=pathlib.Path('/proc/%s/status'%p.pid).read_text();rss=next((int(x.split()[1]) for x in st.splitlines() if x.startswith('VmRSS:')),0);samples.append([time.time(),p.pid,rss]);
   if rss>6*1024**2:p.kill()
  except FileNotFoundError:pass
  time.sleep(.003)
 out=p.stdout.read();err=p.stderr.read();rc=p.wait();writes.append({'file':n,'pid':p.pid,'exit':rc,'samples_epoch_pid_RSS_KiB':samples,'reaped':True,'no_descendants':'writer contains no spawn calls'});assert rc==0,(out,err);return out

def read(p):
 p=pathlib.Path(p).resolve();assert not any(s in str(p).lower() for s in ['crown','bunkbed','tournament']);b=p.read_bytes();reads.append({'path':str(p),'time':time.time(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()});return b
try:
 mode=sys.argv[1]
 if mode=='get':
  for idx,url in enumerate(sys.argv[2:]):
   a={'url':url,'start_UTC_epoch':time.time(),'method':'GET'}
   try:
    with urllib.request.urlopen(url,timeout=35) as f:b=f.read();a.update(status=f.status,finalURL=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),content_type=f.headers.get('Content-Type'))
    name='get-'+str(time.time_ns())+'.base64';write(name,base64.b64encode(b).decode());a['body']=name
    if 'pdf' not in a['content_type'].lower():print(b.decode(errors='replace')[:120000])
   except Exception as e:a.update(error=repr(e))
   a['end_UTC_epoch']=time.time();access.append(a);print('ACCESS',json.dumps(a))
 elif mode=='inventory':
  a=json.loads(read(lane/'frozen-inputs.json'));print('\n'.join(p for p in a if not any(s in p.lower() for s in ['crown','bunkbed','tournament'])))
 elif mode=='bind':
  b=read(root/'1207.0896.pdf.base64');p=base64.b64decode(b);print('PDF_BIND',len(p),hashlib.sha256(p).hexdigest(),p[:12]);a=json.loads(read(root/'raw-provenance.json'))['323739'];raw=a['raw'];print('RAW_BIND',hashlib.sha256(raw.encode()).hexdigest()==a['raw_sha256'],json.loads(raw)==a['parsed']);print('statementSHA',a['statement_sha256'])
 elif mode=='text':
  for p in sys.argv[2:]:print(read(p).decode())
finally:
 u=resource.getrusage(resource.RUSAGE_SELF);rec={'start_UTC_epoch':start,'end_UTC_epoch':time.time(),'reads':reads,'access':access,'writers':writes,'affinity':sorted(os.sched_getaffinity(0)),'CPU_limit_s':120,'AS_limit_bytes':6*1024**3,'CPU_used_s':u.ru_utime+u.ru_stime,'self_peak_RSS_KiB':u.ru_maxrss,'exception':str(sys.exc_info()[1]),'wall_wrapper_s':140};n='audit-'+str(time.time_ns())+'.json';write(n,json.dumps(rec,indent=2));print('AUDIT',n,'RECEIPT_WRITER',json.dumps(writes[-1]))
