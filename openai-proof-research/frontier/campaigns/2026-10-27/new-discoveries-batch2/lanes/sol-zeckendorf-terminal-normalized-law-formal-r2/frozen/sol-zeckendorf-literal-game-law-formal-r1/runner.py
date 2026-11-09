from pathlib import Path
import os,sys,subprocess,resource,time,signal,json,hashlib
L=Path(__file__).resolve().parent
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
LEAN=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
assert hashlib.sha256(LEAN.read_bytes()).hexdigest()=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
env=dict(os.environ,LEAN_PATH=str(Path.cwd())+':'+':'.join(str(p/'.lake/build/lib/lean') for p in sorted(P.iterdir()) if (p/'.lake/build/lib/lean').is_dir()))
def child():
 resource.setrlimit(resource.RLIMIT_AS,(resource.RLIM_INFINITY,resource.RLIM_INFINITY))
 resource.setrlimit(resource.RLIMIT_CPU,(210,210))
cmd=[str(LEAN),'-j1','-M2700','-DwarningAsError=true','-DautoImplicit=false',*sys.argv[1:]]
i=0
while (L/f'attempt-{i:03d}.log').exists():i+=1
log=L/f'attempt-{i:03d}.log';start=time.monotonic();peak=0;reason=None
with log.open('w') as out:
 p=subprocess.Popen(cmd,env=env,stdout=out,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=child)
 while p.poll() is None:
  rss=cpu=0
  for n in os.listdir('/proc'):
   if not n.isdigit():continue
   try:
    s=Path('/proc',n,'stat').read_text().rsplit(')',1)[1].split()
    if int(s[2])==p.pid:
     rss+=int(s[21])*os.sysconf('SC_PAGE_SIZE');cpu+=(int(s[11])+int(s[12]))/os.sysconf('SC_CLK_TCK')
   except (FileNotFoundError,ProcessLookupError,PermissionError):pass
  peak=max(peak,rss)
  if rss>2800*1024**2:reason='RSS'
  if cpu>210:reason='CPU'
  if time.monotonic()-start>230:reason='wall'
  if reason:os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.04)
 code=p.wait()
r=dict(command=cmd,exit=code,reason=reason,peak_group_rss=peak,seconds=time.monotonic()-start,serial=True)
log.with_suffix('.json').write_text(json.dumps(r,indent=2)+'\n')
print(log.read_text());print(json.dumps(r));sys.exit(code if code>=0 else 128-code)
