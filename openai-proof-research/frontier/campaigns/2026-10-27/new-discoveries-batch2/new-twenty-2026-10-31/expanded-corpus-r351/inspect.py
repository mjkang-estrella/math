import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib
exec(compile((pathlib.Path(__file__).parent/'worker.py').read_text().split('code=0')[0],'worker.py','exec'))
try:
 if sys.argv[1]=='windows':
  r=json.loads(read(P/'reservation.json'));inv=[]
  for row in r['rows']:
   name=row['source_url'].rsplit('/',1)[1]+'.html.txt';t=read(P/'sources'/name).decode(); pat=sys.argv[2] if len(sys.argv)>2 else 'Conjecture'; hits=list(re.finditer(pat,t,re.I)); ranges=[]
   for m in hits[:8]:
    a=max(0,m.start()-350);b=min(len(t),m.end()+1400)
    if ranges and a<ranges[-1][1]:ranges[-1][1]=b
    else:ranges.append([a,b])
   print('\nID',row['mathdb_id'],'FILE',name,'chars',len(t));
   for a,b in ranges:print('RANGE',a,b,t[a:b])
   inv.append({'id':row['mathdb_id'],'file':name,'ranges':ranges,'depth':'conjecture-context windows, not full proof review'})
  save('read-windows-'+token+'.json',inv)
 elif sys.argv[1]=='slice':
  t=read(P/sys.argv[2]).decode();a=int(sys.argv[3]);b=int(sys.argv[4]);print(t[a:b]);save('read-slice-'+token+'.json',{'file':sys.argv[2],'range':[a,b]})
 elif sys.argv[1]=='history':
  h=json.loads(read(P/'history-matches.json'))
  for x in h:
   print(x['path'].split('/')[-2]);t=json.dumps(x['body'],ensure_ascii=False)
   for family in x['families']:
    m=re.search(re.escape(family),t,re.I)
    if m:print(t[max(0,m.start()-350):m.end()+2300])
finally:
 u=resource.getrusage(resource.RUSAGE_SELF);save('receipts/process-'+token+'.json',{'argv':sys.argv,'true_python_exit':0,'wall':time.monotonic()-started,'affinity':sorted(os.sched_getaffinity(0)),'cpu_limit':120,'AS_limit':6*1024**3,'wall_limit':140,'self_cpu':u.ru_utime+u.ru_stime,'self_peak_RSS_KiB':u.ru_maxrss,'reads':reads,'limit':'self only; no child processes'})
