import os,sys,subprocess,resource,time,pathlib,json,signal,datetime
R=pathlib.Path(__file__).resolve().parents[1]
def run(label,cmd,cwd=None,env=None):
 def limits():
  os.setsid();os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(64*1024**3,64*1024**3))
 start=time.monotonic();peak=0;why=None
 with (R/'logs'/f'{label}.log').open('w') as f:
  p=subprocess.Popen(cmd,cwd=cwd,env=env,preexec_fn=limits,stdout=f,stderr=subprocess.STDOUT)
  while p.poll() is None:
   rss=0
   for d in pathlib.Path('/proc').glob('[0-9]*'):
    try:
     s=(d/'stat').read_text().rsplit(')',1)[1].split()
     if int(s[2])==p.pid:
      rss+=sum(int(l.split()[1])*1024 for l in (d/'status').read_text().splitlines() if l.startswith(('RssAnon:','RssShmem:')))
    except (OSError,ValueError):pass
   peak=max(peak,rss)
   if rss>6*1024**3 or time.monotonic()-start>140:
    why='RSS or wall cap';os.killpg(p.pid,signal.SIGKILL);break
   time.sleep(.05)
  p.wait()
 receipt=dict(utc=str(datetime.datetime.now(datetime.timezone.utc)),command=cmd,exit=p.returncode,wall=time.monotonic()-start,peak_private=peak,killed=why,cpu_cap=120,wall_cap=140,as_cap=64*1024**3,rss_cap=6*1024**3,cpu_affinity=sorted(os.sched_getaffinity(0))[:2],systemd=bool(cmd and cmd[0]=='systemd-run'))
 (R/'receipts'/f'{label}.json').write_text(json.dumps(receipt,indent=2));print(label,receipt,flush=True)
 return p.returncode
if __name__=='__main__':
 B='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin'
 P=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
 F=R/'fresh/proof';E=os.environ.copy();E.update(LEAN_PATH=':'.join([str(F)]+[str(p) for p in P.glob('*/.lake/build/lib/lean')]),LEAN_NUM_THREADS='1',MALLOC_ARENA_MAX='2')
 assert run('strict-build',[B+'/lean','-j1','-DwarningAsError=true','-o','MathDB378395.olean','MathDB378395.lean'],F,E)==0
 assert run('leanchecker',[B+'/leanchecker','MathDB378395'],F,E)==0
 for name in ['ReviewAudit','ReviewSanity']:
  assert run(name,[B+'/lean','-j1','-DwarningAsError=true',name+'.lean'],F,E)==0
