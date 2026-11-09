import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,subprocess,json,sys,time,re
L=pathlib.Path(__file__).resolve().parent;t=time.monotonic();out=[]
if sys.argv[1]=='convert':
 for p in (L/'sources').glob('*.pdf'):
  q=p.with_suffix('.txt');assert q.resolve().is_relative_to(L)
  r=subprocess.run(['pdftotext','-layout',str(p),str(q)],capture_output=True,timeout=15);out.append({'source':p.name,'exit':r.returncode,'stderr':r.stderr.decode(),'bytes':q.stat().st_size if q.exists() else None})
else:
 for arg in sys.argv[1:]:
  name,pattern=arg.split(':',1);p=L/'sources'/name;lines=p.read_text().splitlines();print('\nSOURCE',name,'LINES',len(lines))
  if pattern=='FULL':ranges=[(0,len(lines))]
  elif re.fullmatch(r'\d+-\d+',pattern):a,b=map(int,pattern.split('-'));ranges=[(a-1,b)]
  else:ranges=[(max(0,i-8),min(len(lines),i+23)) for i,s in enumerate(lines) if re.search(pattern,s,re.I)]
  seen=set()
  for a,b in ranges:
   for i in range(a,b):
    if i not in seen:print(str(i+1)+': '+lines[i]);seen.add(i)
  out.append({'source':name,'pattern':pattern,'printed_lines':sorted(i+1 for i in seen),'meaning':'actual displayed text; not a full-source read unless all lines displayed'})
p=(L/('process-read-'+str(os.getpid())+'.json')).resolve();p.write_text(json.dumps({'exit':0,'elapsed':time.monotonic()-t,'operations':out,'affinity':sorted(os.sched_getaffinity(0)),'self_maxrss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'children_reaped':True,'child_maxrss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'scope':'self/reaped-child, not concurrent group peak'},indent=2)+'\n')
