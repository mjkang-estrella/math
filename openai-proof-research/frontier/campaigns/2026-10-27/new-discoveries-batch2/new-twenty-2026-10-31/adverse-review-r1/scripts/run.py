import os,sys,time,signal,resource,subprocess,json
from pathlib import Path
R=Path(__file__).resolve().parents[1]
BIN=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
PKG=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
def run(label,args):
 env={k:v for k,v in os.environ.items() if k not in ['LEAN_PATH','LEAN_SRC_PATH','LEAN_PLUGIN_PATH','LEAN_OPTS','LD_PRELOAD']}
 env.update(LEAN_PATH=':'.join([str(R/'extracted/formal')]+[str(p) for p in PKG.glob('*/.lake/build/lib/lean')]),PATH=str(BIN)+':'+env['PATH'],TMPDIR=str(R/'tmp'),MALLOC_ARENA_MAX='2',LEAN_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1')
 def lim():
  os.setsid();os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120))
 start=time.monotonic();peak=0;reason=None
 with (R/'logs'/f'{label}.log').open('w') as f:
  p=subprocess.Popen(args,cwd=R/'extracted',env=env,preexec_fn=lim,stdout=f,stderr=subprocess.STDOUT)
  while p.poll() is None:
   rss=0
   for q in Path('/proc').glob('[0-9]*'):
    try:
     if os.getpgid(int(q.name))==p.pid:
      rss+=sum(int(l.split()[1])*1024 for l in (q/'smaps_rollup').read_text().splitlines() if l.startswith(('Private_Clean:','Private_Dirty:','Private_Hugetlb:')))
    except (OSError,ValueError):pass
   peak=max(peak,rss)
   if rss>6*1024**3:reason='RSS'
   if time.monotonic()-start>140:reason='wall'
   if reason:os.killpg(p.pid,signal.SIGKILL);break
   time.sleep(.1)
  rc=p.wait()
  try:os.killpg(p.pid,signal.SIGKILL)
  except ProcessLookupError:pass
 receipt=dict(command=args,exit=rc,termination=reason,seconds=time.monotonic()-start,peak_private_rss=peak,cpu_limit=120,wall_limit=140,max_cpus=2)
 (R/'receipts'/f'{label}.json').write_text(json.dumps(receipt,indent=2));print(label,rc,round(receipt['seconds'],2),peak,flush=True)
 return rc
if __name__=='__main__':
 mods=['Definitions','Certificates','Gram','Independence']+[f'Deletion{i}' for i in range(6)]+['Bridges','Quadratic','Main']
 assert not list((R/'extracted').rglob('*.olean'))
 for m in mods:
  assert run('build-'+m,[str(BIN/'lean'),'-j1','-DwarningAsError=true','-o',f'formal/{m}.olean',f'formal/{m}.lean'])==0
  assert run('check-'+m,[str(BIN/'leanchecker'),m])==0
