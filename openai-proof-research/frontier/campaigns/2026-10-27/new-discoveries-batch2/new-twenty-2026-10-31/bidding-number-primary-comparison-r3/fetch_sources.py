import os,resource
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(110,110));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import sys,time,json,pathlib,urllib.request,urllib.error,hashlib,subprocess,threading,uuid
lane=pathlib.Path(__file__).resolve().parent
peak=[0]; stop=threading.Event()
def sample():
 while not stop.is_set():
  try: peak[0]=max(peak[0],int(pathlib.Path('/proc/self/statm').read_text().split()[1])*os.sysconf('SC_PAGE_SIZE'))
  except Exception: pass
  stop.wait(.05)
t=threading.Thread(target=sample);t.start();records=[]
def write(name,s):
 p=subprocess.run([sys.executable,'-I','-B',str(lane/'write_lane.py'),name],input=s,text=True,capture_output=True,timeout=15);assert p.returncode==0,p.stderr
for item in sys.argv[1:]:
 name,url=item.split('=',1);r={'id':str(uuid.uuid4()),'name':name,'url':url,'method':'GET','utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())};start=time.monotonic()
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'PrimarySourceComparison/1.0'}),timeout=22) as f:
   data=f.read(12000000);r.update(status=f.status,final_url=f.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest(),content_type=f.headers.get('Content-Type'))
  if data.startswith(b'%PDF'):
   p=subprocess.run(['pdftotext','-layout','-','-'],input=data,capture_output=True,timeout=25);r['pdftotext_exit']=p.returncode;text=p.stdout.decode('utf-8','replace')
  else:text=data.decode('utf-8','replace')
  write('sources/'+name+'.txt',text);r['stored']='sources/'+name+'.txt';r['read_depth']='retrieved/converted only; selective cognitive reading recorded separately'
 except urllib.error.HTTPError as e:r.update(status=e.code,final_url=e.url,error=str(e))
 except Exception as e:r.update(status=None,error=repr(e))
 r['elapsed_s']=time.monotonic()-start;records.append(r);print(json.dumps(r))
stop.set();t.join()
write('access-'+str(uuid.uuid4())+'.json',json.dumps({'requests':records,'caps_before_reads':True,'affinity':list(os.sched_getaffinity(0)),'cpu_limit_s':110,'as_limit_bytes':6*1024**3,'self_sample_peak_rss_bytes':peak[0],'self_highwater_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'threads_joined':True,'subprocesses_reaped':True,'exit_at_receipt':0},indent=2))
