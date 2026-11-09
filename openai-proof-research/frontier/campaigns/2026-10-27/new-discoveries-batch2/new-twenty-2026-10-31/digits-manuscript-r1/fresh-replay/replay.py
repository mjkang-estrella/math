#!/usr/bin/env python3
"""Fresh sequential replay. All outputs remain in the extraction."""
from pathlib import Path
import os, sys, json, subprocess, hashlib, resource, time, signal, re
W=Path(__file__).resolve().parent
os.chdir(W)
if any(W.rglob('*.olean*')):sys.exit('REFUSED: existing oleans')
for d in ['logs','receipts','tmp']:(W/d).mkdir(exist_ok=True)
B=Path(os.environ['LEAN_BIN']).resolve(); P=Path(os.environ['LEAN_PACKAGES']).resolve()
env=os.environ.copy()
for k in ['LEAN_PATH','LEAN_SRC_PATH','LEAN_PLUGIN_PATH','LD_PRELOAD','LEAN_OPTS']:env.pop(k,None)
env.update(LEAN_PATH=':'.join([str(W/'formal')]+[str(p/'.lake/build/lib/lean') for p in sorted(P.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]),PATH=str(B)+':'+env['PATH'],MALLOC_ARENA_MAX='2',LEAN_NUM_THREADS='1',TMPDIR=str(W/'tmp'),PYTHONDONTWRITEBYTECODE='1')
def limits():
 os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120))
def run(label,cmd,expected=0):
 start=time.monotonic();peak=0;killed=None
 with (W/'logs'/f'{label}.log').open('w') as f:
  p=subprocess.Popen(cmd,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=limits)
  while p.poll() is None:
   # Sum resident memory of the process group, counting shared pages conservatively.
   rss=0
   for proc in Path('/proc').iterdir():
    if not proc.name.isdigit():continue
    try:
     if os.getpgid(int(proc.name)) != p.pid:continue
     for line in (proc/'status').read_text().splitlines():
      if line.startswith('VmRSS:'):rss+=int(line.split()[1])
    except (OSError,ValueError,ProcessLookupError):pass
   peak=max(peak,rss)
   if rss>6*1024*1024 or time.monotonic()-start>140:
    killed='RSS or wall cap';os.killpg(p.pid,signal.SIGKILL);break
   time.sleep(.1)
  p.wait()
 r=dict(command=list(map(str,cmd)),returncode=p.returncode,seconds=time.monotonic()-start,peak_RSS_KiB=peak,killed=killed,cpu_limit_s=120,wall_limit_s=140,affinity_cpus=2)
 (W/'receipts'/f'{label}.json').write_text(json.dumps(r,indent=2)+'\n')
 if p.returncode!=expected or killed:raise RuntimeError(label+' failed; see logs')
 return r
for file,h in json.loads((W/'SOURCE-MANIFEST.json').read_text()).items():
 assert hashlib.sha256((W/file).read_bytes()).hexdigest()==h,file
run('version',[str(B/'lean'),'--version'])
v=(W/'logs/version.log').read_text();assert '4.34.1' in v and '5045d0056413266e57c625dcd7c365b10e377c52' in v
for m in ['Digits','Audit','AuditFull']:
 if m=='Digits':assert not re.search(r'\b(sorry|admit|axiom|unsafe|partial|native_decide|ofReduceBool|implemented_by|extern)\b',(W/'formal/Digits.lean').read_text())
 run('build-'+m,[str(B/'lean'),'-j1','-DwarningAsError=true',f'formal/{m}.lean','-o',f'formal/{m}.olean'])
 run('check-'+m,[str(B/'leanchecker'),m])
s=(W/'logs/build-AuditFull.log').read_text()
assert 'AUDITED_LOCAL_DECLARATIONS|45' in s
assert s.count('TYPE|')==45 and s.count('BODY|')==45 and s.count('DECL|')==45
for m in ['ExtraDigit','QuadraticOnly']:
 run('negative-'+m,[str(B/'lean'),'-j1','-DwarningAsError=true',f'negative/{m}.lean'],1)
 s=(W/'logs'/f'negative-{m}.log').read_text();assert 'error:' in s and ('unsolved goals' in s or 'false' in s or 'not true' in s)
p=subprocess.run([sys.executable,'-I',str(W/'replay.py')],env=env,capture_output=True,text=True)
assert p.returncode!=0 and 'REFUSED: existing oleans' in p.stderr
(W/'logs/freshness-negative.log').write_text(p.stdout+p.stderr)
(W/'receipts/replay.json').write_text(json.dumps(dict(status='PASS',modules=['Digits','Audit','AuditFull'],declarations=45,types=45,bodies=45,negative_controls=2,freshness_refusal='PASS',trusted_axioms=['propext','Classical.choice','Quot.sound']),indent=2)+'\n')
print('PASS: strict replay, three leanchecker modules, 45 full declarations, two negative controls')
