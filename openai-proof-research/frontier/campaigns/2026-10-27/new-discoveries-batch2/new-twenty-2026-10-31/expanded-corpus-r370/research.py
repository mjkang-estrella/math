import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,subprocess,time,threading,hashlib,datetime,urllib.request,base64,sys
L=pathlib.Path(__file__).resolve().parent
receipts=[]
def run(args,data):
 p=subprocess.Popen(args,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE);box={};peak=0;start=time.monotonic()
 def worker():box['out'],box['err']=p.communicate(data)
 t=threading.Thread(target=worker);t.start()
 while t.is_alive():
  try:
   rss=int(pathlib.Path(f'/proc/{p.pid}/status').read_text().split('VmRSS:')[1].split()[0]);peak=max(peak,rss)
   if rss>1024*1024 or time.monotonic()-start>45:p.kill()
  except (FileNotFoundError,IndexError,ProcessLookupError):pass
  t.join(.01)
 t.join();p.wait();receipts.append({'argv':args,'exit':p.returncode,'sampled_child_RSS_KiB':peak,'wall_s':time.monotonic()-start});assert p.returncode==0,box['err'];return box['out']
def write(name,obj):
 s=obj if isinstance(obj,str) else json.dumps(obj,ensure_ascii=False,indent=2)+'\n'
 run(['python3','-I','-B',str(L/'write_lane.py'),name],s.encode())
http=[]
def fetch(url,name,pdf=False):
 row={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};start=time.monotonic()
 try:
  op=urllib.request.build_opener(urllib.request.ProxyHandler({}))
  with op.open(urllib.request.Request(url,headers={'User-Agent':'ordinary-mathematical-source-review/1.0'}),timeout=18) as r:b=r.read(16000000);row.update(status=r.status,final_url=r.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  write(name+'.source.b64',base64.b64encode(b).decode())
  text=run(['pdftotext','-layout','-','-'],b).decode() if pdf else b.decode(errors='replace')
  write(name+'.txt',text);row.update(artifact=name+'.txt',acquisition_depth='full bytes and converted full text; agent passage read recorded separately');print(name,len(text))
 except Exception as e:row.update(error=repr(e));print(name,'ERROR',repr(e))
 row['wall_s']=time.monotonic()-start;http.append(row)
if __name__=='__main__':
 for a in sys.argv[1:]:fetch('https://arxiv.org/pdf/'+a,a,True)
 write('http-'+str(time.time_ns())+'.json',http)
 write('resources-'+str(time.time_ns())+'.json',{'children':receipts.copy(),'affinity':sorted(os.sched_getaffinity(0)),'CPU_limit_s':120,'AS_limit_bytes':6*1024**3,'wall_timeout_s':140,'all_children_joined_reaped':True,'self_usage':list(resource.getrusage(resource.RUSAGE_SELF)),'self_peak_not_group':True,'exit':0})
