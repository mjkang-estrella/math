import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,time,subprocess,urllib.request
P=pathlib.Path(__file__).resolve().parent
OPS=[]
def utc(): return time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())
def sha(b): return hashlib.sha256(b).hexdigest()
def read(f):
 f=pathlib.Path(f); b=f.read_bytes();OPS.append(dict(kind='read',path=str(f),utc=utc(),bytes=len(b),sha256=sha(b),depth='full byte acquisition; semantic depth separately recorded',pid=os.getpid(),rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss));return b
def proc(cmd,data=None):
 t=time.monotonic();q=subprocess.Popen(cmd,stdin=subprocess.PIPE if data is not None else subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.PIPE); samples=[]
 while True:
  try:
   st=pathlib.Path('/proc/'+str(q.pid)+'/status').read_text(); samples.append({k:v.strip() for k,v in (line.split(':',1) for line in st.splitlines() if line.startswith(('VmRSS:','Cpus_allowed_list:','PPid:')))})
   if int(next((x.split()[1] for x in st.splitlines() if x.startswith('VmRSS:')),'0'))>6*1024**2:q.kill()
  except FileNotFoundError:pass
  try:out,err=q.communicate(data,timeout=.02);break
  except subprocess.TimeoutExpired:data=None
  if time.monotonic()-t>125:q.kill();out,err=q.communicate();break
 OPS.append(dict(kind='child',argv=cmd,pid=q.pid,utc=utc(),exit=q.returncode,samples=samples,wall=time.monotonic()-t,stderr=err.decode(errors='replace')))
 if q.returncode:raise RuntimeError(err.decode())
 return out
def write(n,s):
 if not isinstance(s,str):s=json.dumps(s,ensure_ascii=False,indent=2)+'\n'
 return proc(['python3','-I','-B',str((P/'write_lane.py').resolve()),n],s.encode())
def finish(tag):
 r=dict(utc=utc(),pid=os.getpid(),affinity=list(os.sched_getaffinity(0)),cpu_limit=resource.getrlimit(resource.RLIMIT_CPU),AS_limit=resource.getrlimit(resource.RLIMIT_AS),self_rusage=list(resource.getrusage(resource.RUSAGE_SELF)),operations=OPS,limitations='self high-water for reader; sampled actual direct children, no spawned grandchildren expected; receipt writer terminal exit printed separately; true enclosing exit in tool output')
 write('receipts/'+tag+'.json',r);print('TERMINAL',json.dumps(OPS[-1]),flush=True)
def fetch(url,n):
 t=utc();r=dict(kind='HTTP GET',url=url,utc=t)
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'SourceResearch/1.0'}),timeout=25) as z:b=z.read();r.update(status=z.status,final_url=z.url,bytes=len(b),sha256=sha(b))
  if b.startswith(b'%PDF'):proc(['python3','-I','-B',str(P/'write_lane.py'),n+'.b64'],__import__('base64').b64encode(b));r['encoding']='base64';r['path']=n+'.b64'
  else:write(n,b.decode('utf-8',errors='replace'));r['path']=n
 except Exception as e:r['error']=str(e);b=b''
 OPS.append(r);return b,r
