import os,sys,subprocess,time,resource,json,signal
from pathlib import Path
D=Path(__file__).resolve().parents[1]
packages=os.environ.get('LEAN_PACKAGES','/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
lean=os.environ.get('LEAN_BIN','/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
env=dict(os.environ);env.update(PATH=str(Path(lean).parent)+':'+env.get('PATH',''),MALLOC_ARENA_MAX='2',TMPDIR=str(D/'outputs'),LEAN_PATH=':'.join([str(D/'formal')]+[str(p) for p in Path(packages).glob('*/.lake/build/lib/lean')]))
def limits():
 resource.setrlimit(resource.RLIMIT_CPU,(120,120)); os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
args=sys.argv[1:]; name=os.environ.get('RUN_NAME','lean'); log=D/'logs'/f'{name}.log'
cmd=[lean,'-j1','-DwarningAsError=true']+args
if args and args[0]=='--checker':cmd=[str(Path(lean).with_name('leanchecker'))]+args[1:]
start=time.monotonic();peak=0;killed=None
with log.open('w') as out:
 p=subprocess.Popen(cmd,cwd=D/'formal',env=env,stdout=out,stderr=subprocess.STDOUT,preexec_fn=limits,start_new_session=True)
 while p.poll() is None:
  try:
   rss=0
   for proc in Path('/proc').iterdir():
    if not proc.name.isdecimal():continue
    try:
     if os.getpgid(int(proc.name))!=p.pid:continue
     vals=(proc/'smaps_rollup').read_text().splitlines()
     rss+=sum(int(x.split()[1]) for x in vals if x.startswith(('Private_Clean:','Private_Dirty:','Private_Hugetlb:')))*1024
    except (OSError,ProcessLookupError):pass
   peak=max(peak,rss)
   if rss>6*1024**3:killed='private RSS'
  except (FileNotFoundError, ProcessLookupError):pass
  if time.monotonic()-start>140:killed='wall'
  if killed:os.killpg(p.pid,signal.SIGKILL)
  time.sleep(.05)
 rc=p.wait()
r={'command':args,'returncode':rc,'seconds':time.monotonic()-start,'peak_private_rss':peak,'killed':killed};(D/'receipts'/f'{name}.json').write_text(json.dumps(r,indent=2));print(json.dumps(r));print(log.read_text()[-15000:]);sys.exit(rc)
