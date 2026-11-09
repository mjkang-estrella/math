from pathlib import Path
import os,sys,json,time,subprocess,resource,hashlib
ROOT=Path(__file__).resolve().parents[1]; F=ROOT/'fresh'
BIN=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
CACHE=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
os.environ.update(MALLOC_ARENA_MAX='2',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OPENBLAS_NUM_THREADS='1')
os.environ['PATH']=str(BIN)+':/usr/bin:/bin'
os.environ['LEAN_PATH']=':'.join([str(F)]+[str(x/'.lake/build/lib/lean') for x in sorted(CACHE.iterdir()) if x.is_dir()])
def limit():
 os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(64<<30,64<<30))
def run(label,cmd,expected=0):
 t=time.monotonic(); peak=0
 with (ROOT/'logs'/f'{label}.log').open('w') as log:
  p=subprocess.Popen(cmd,cwd=F,stdout=log,stderr=subprocess.STDOUT,preexec_fn=limit)
  while p.poll() is None:
   try:
    def subtree(pid):
     ids={pid}
     for child in Path(f'/proc/{pid}/task/{pid}/children').read_text().split(): ids.update(subtree(int(child)))
     return ids
    ids=subtree(p.pid)
    rss=sum(int(Path(f'/proc/{pid}/status').read_text().split('VmRSS:')[1].split()[0])*1024 for pid in ids)
    peak=max(peak,rss)
   except (FileNotFoundError,IndexError,ProcessLookupError): pass
   if peak>6<<30 or time.monotonic()-t>140:
    for pid in locals().get('ids',{p.pid}):
     try: os.kill(pid,9)
     except ProcessLookupError: pass
   time.sleep(.03)
  code=p.wait()
 row=dict(label=label,command=cmd,exit=code,expected=expected,wall=time.monotonic()-t,peak_RSS_bytes=peak)
 with (ROOT/'logs/results.jsonl').open('a') as out: out.write(json.dumps(row)+'\n')
 print(label,code,flush=True)
 assert (code==0 if expected==0 else code!=0), row
if __name__=='__main__':
 pins=json.loads((F/'pins.json').read_text())
 for name in ['lean','leanchecker']: assert hashlib.sha256((BIN/name).read_bytes()).hexdigest()==pins[name+'_binary_sha256']
 assert hashlib.sha256((CACHE/'mathlib/.lake/build/lib/lean/Mathlib.olean').read_bytes()).hexdigest()==pins['mathlib_root_olean_sha256']
 for name,digest in json.loads((F/'MANIFEST.json').read_text())['files'].items(): assert hashlib.sha256((F/name).read_bytes()).hexdigest()==digest,name
 modules=['Basic','Identity','Attainment','PathExtension','Structure','DartDeficit','ConfigurationCount','Gap','Bracketing','BipartitionValue','Endpoint']
 for m in modules:
  run(m,[str(BIN/'lean'),'-j1','-DwarningAsError=true','-o',f'Sigma/{m}.olean',f'Sigma/{m}.lean'])
  run(m+'-checker',[str(BIN/'leanchecker'),'Sigma.'+m])
