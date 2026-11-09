import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(110,110));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,time,sys,subprocess,urllib.request,datetime
L=pathlib.Path(__file__).resolve().parent; A=L.parent/'expanded-corpus-r369'
start=time.monotonic(); items=[]; stamp=str(time.time_ns())
def write(name,data):
 p=subprocess.Popen([sys.executable,'-I','-B',str(L/'write_lane.py'),name],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
 p.stdin.write(data);p.stdin.close(); peak=0
 while p.poll() is None:
  try:
   status=pathlib.Path('/proc/'+str(p.pid)+'/status').read_text(); rss=int(status.split('VmRSS:')[1].split()[0]) if 'VmRSS:' in status else 0;peak=max(peak,rss)
   if rss>524288 or time.monotonic()-t>130:p.kill()
  except FileNotFoundError:pass
  time.sleep(.005)
 out=p.stdout.read();err=p.stderr.read();rc=p.wait();items.append({'writer':name,'exit':rc,'sampled_peak_RSS_KiB':peak,'stderr':err});assert rc==0

t=time.monotonic()
def read(p):
 p=pathlib.Path(p);assert not any(s in str(p).lower() for s in ['crown','transitive-bunkbed']);b=p.read_bytes();items.append({'read':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()});return b.decode()
try:
 mode=sys.argv[1]
 if mode=='read':
  for name in sys.argv[2:]:
   p=A/name;print('FILE',p);print(read(p))
 elif mode=='windows':
  name=sys.argv[2];s=read(A/name);lines=s.splitlines();import re
  terms=sys.argv[3:];inds=set()
  for i,line in enumerate(lines):
   if any(re.search(q,line,re.I) for q in terms):inds.update(range(max(0,i-7),min(len(lines),i+16)))
  for i in sorted(inds):print(str(i+1)+': '+lines[i])
 elif mode=='fetch':
  name,url=sys.argv[2:];rec={'url':url,'UTC':datetime.datetime.now(datetime.timezone.utc).isoformat()};op=urllib.request.build_opener(urllib.request.ProxyHandler({}))
  try:
   with op.open(url,timeout=35) as r:
    b=r.read(20*1024*1024);rec.update(status=r.status,finalURL=r.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),content_type=r.headers.get('Content-Type'));import base64;write('fresh/'+name+'.b64',base64.b64encode(b).decode());print(b.decode(errors='replace')[:100000] if 'pdf' not in rec['content_type'] else 'PDF cached')
  except Exception as e:rec['error']=repr(e)
  items.append(rec);print(json.dumps(rec))
finally:
 usage=resource.getrusage(resource.RUSAGE_SELF);rec={'id':stamp,'argv':sys.argv,'items':items,'wall':time.monotonic()-start,'CPU':usage.ru_utime+usage.ru_stime,'self_peak_RSS_KiB':usage.ru_maxrss,'affinity':sorted(os.sched_getaffinity(0)),'CPU_cap':110,'AS_cap':6*1024**3,'completed':True,'telemetry_limit':'self highwater and sampled writer child only, not cgroup telemetry'}
 write('receipts/'+stamp+'.json',json.dumps(rec,indent=2)+'\n')
