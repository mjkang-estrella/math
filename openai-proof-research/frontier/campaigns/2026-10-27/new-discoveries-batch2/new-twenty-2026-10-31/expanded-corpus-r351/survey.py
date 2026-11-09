import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib
exec(compile((pathlib.Path(__file__).parent/'worker.py').read_text().split('code=0')[0],'worker.py','exec'))
inv=[]
if sys.argv[1]=='compact':
 for row in json.loads(read(P/'reservation.json'))['rows']:
  f='sources/'+row['source_url'].rsplit('/',1)[1]+'.html.txt';t=read(P/f).decode();ms=list(re.finditer(r'(?:Conjecture|Question) \d[^\n]*\.',t));ms=ms[:2]; print('\nID',row['mathdb_id']); ranges=[]
  for m in ms:
   a=max(0,m.start()-100);b=min(len(t),m.start()+1600);print(t[a:b]);ranges.append([a,b])
  inv.append({'id':row['mathdb_id'],'file':f,'ranges':ranges})
elif sys.argv[1]=='locate':
 for fn in sys.argv[2:]:
  t=read(P/fn).decode(); print('\nFILE',fn)
  for pat in ['currentOid','Submission history','Journal','Proposition 1.5','Theorem 5.2','Theorem 1','Conjecture 4','3.1','two-hole','files/','projects/','candidates/']:
   ms=list(re.finditer(re.escape(pat),t,re.I))[:3]
   for m in ms:print('OFFSET',m.start(),t[max(0,m.start()-120):m.end()+600])
  inv.append({'file':fn,'depth':'located bounded matching passages'})
u=resource.getrusage(resource.RUSAGE_SELF);save('receipts/process-'+token+'.json',{'exit':0,'argv':sys.argv,'limits':[2,120,140,6*1024**3],'affinity':sorted(os.sched_getaffinity(0)),'self_cpu':u.ru_utime+u.ru_stime,'wall':time.monotonic()-started,'self_peak_RSS_KiB':u.ru_maxrss,'reads':reads,'display':inv,'telemetry':'self only; no children'})
