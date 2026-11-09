import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,sys,time,datetime,urllib.request,urllib.error,subprocess
p=pathlib.Path(__file__).resolve().parent
start=time.monotonic()
try:
 if sys.argv[1]=='get':
  url=sys.argv[2]; name=sys.argv[3]; r={'url':url,'method':'GET','utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  try:
   with urllib.request.urlopen(url,timeout=35) as f:
    b=f.read(20000001);assert len(b)<=20000000;r.update(status=f.status,final_url=f.url,headers=dict(f.headers),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
   (p/name).write_bytes(b);r['path']=name
   if b.startswith(b'%PDF'):
    subprocess.run(['pdftotext','-layout',str(p/name),str(p/(name+'.txt'))],timeout=25,check=True);r['text_path']=name+'.txt'
  except Exception as e:
   r['error']=str(e)
   if isinstance(e,urllib.error.HTTPError):
    b=e.read(1000000);r.update(status=e.code,headers=dict(e.headers),bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(p/(name+'.error')).write_bytes(b)
  with (p/'http-receipts.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
  print(json.dumps(r))
 elif sys.argv[1]=='read':
  f=p/sys.argv[2];lines=f.read_text().splitlines();lo=int(sys.argv[3]);hi=int(sys.argv[4]);print('FILE',f,'TOTAL_LINES',len(lines));print('\n'.join(str(i+1)+': '+v for i,v in enumerate(lines) if lo<=i+1<=hi))
 elif sys.argv[1]=='freeze':
  m=json.loads((p/'frozen-inputs.json').read_text());assert not any('crown-vnumber-' in x or 'expanded-corpus-r327' in x for x in m);r={x:hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest()==h for x,h in m.items()};assert len(r)==139 and all(r.values());(p/'frozen-after.json').write_text(json.dumps({'count':len(r),'all_match':True,'checks':r},indent=2)+'\n');print('AFTER 139/139 PASS')
finally:
 u=resource.getrusage(resource.RUSAGE_SELF);c=resource.getrusage(resource.RUSAGE_CHILDREN)
 with (p/'resource-jobs.jsonl').open('a') as f:f.write(json.dumps({'argv':sys.argv,'affinity':sorted(os.sched_getaffinity(0)),'wall_s':time.monotonic()-start,'self_CPU_s':u.ru_utime+u.ru_stime,'self_peak_RSS_KiB':u.ru_maxrss,'reaped_children_CPU_s':c.ru_utime+c.ru_stime,'children_peak_RSS_KiB':c.ru_maxrss,'CPU_limit_s':120,'AS_limit_bytes':6*1024**3,'external_wall_timeout_s':140,'group_telemetry':'unavailable'})+'\n')
