import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import urllib.request,pathlib,json,time,hashlib,sys,subprocess,threading
lane=pathlib.Path(__file__).resolve().parent
samples=[];stop=threading.Event()
def sample():
 while not stop.is_set():
  samples.append(int(pathlib.Path('/proc/self/statm').read_text().split()[1])*os.sysconf('SC_PAGE_SIZE'));stop.wait(.1)
t=threading.Thread(target=sample);t.start();rows=[]
def put(name,s):subprocess.run([sys.executable,'-I','-B',str(lane/'write_lane.py'),name],input=s,text=True,check=True,stdout=subprocess.DEVNULL)
try:
 for name,url in [('openai','https://github.com/OpenAI/math'),('leanpool','https://github.com/LeanPool/lean-pool'),('arxiv','https://arxiv.org/abs/2207.11596')]:
  r={'id':name+'-get-1','url':url,'method':'GET','utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}
  try:
   with urllib.request.urlopen(url,timeout=20) as h:
    r.update(status=h.status,final_url=h.url);b=h.read(3000000);r.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest());put('sources/'+name+'.html',b.decode());r['stored']='sources/'+name+'.html'
  except Exception as e:r['error']=repr(e)
  rows.append(r)
finally:
 stop.set();t.join()
 put('access.json',json.dumps({'requests':rows,'caps_before_reads':True,'allowed_cpus':sorted(os.sched_getaffinity(0)),'self_sample_peak_rss_bytes':max(samples,default=0),'self_high_water_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'threads_joined':True,'children_reaped':True},indent=2)+'\n')
print(json.dumps(rows))
