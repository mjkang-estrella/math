import os,resource,subprocess,pathlib,sys,time,json,signal
D=pathlib.Path(__file__).resolve().parents[1];P=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages');B=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin');env={'PATH':str(B)+':/usr/bin:/bin','HOME':str(pathlib.Path.home()),'LANG':'C.UTF-8','MALLOC_ARENA_MAX':'2','LEAN_PATH':':'.join([str(D/'lean')]+[str(x/'.lake/build/lib/lean') for x in sorted(P.iterdir()) if x.is_dir()])};cpus=sorted(os.sched_getaffinity(0))[:2]
def limit():
 os.sched_setaffinity(0,cpus);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(64*1024**3,64*1024**3))
args=sys.argv[1:];checker=args and args[0]=='--checker'
cmd=[str(B/'leanchecker'),*args[1:]] if checker else [str(B/'lean'),'-j1','-DwarningAsError=true',*args]
start=time.monotonic();peak=0;reason=None;p=subprocess.Popen(cmd,cwd=D/'lean',env=env,preexec_fn=limit,start_new_session=True)
while p.poll() is None:
 try:
  data=pathlib.Path(f'/proc/{p.pid}/smaps_rollup').read_text();private=sum(int(l.split()[1])*1024 for l in data.splitlines() if l.startswith(('Private_Clean:','Private_Dirty:')));peak=max(peak,private)
 except (FileNotFoundError,ProcessLookupError):pass
 if peak>6*1024**3 or time.monotonic()-start>140:
  reason='private RSS or wall limit';os.killpg(p.pid,signal.SIGKILL)
 time.sleep(.025)
rc=p.wait();(D/'outputs').mkdir(exist_ok=True);name=('checker-' if checker else 'lean-')+pathlib.Path(args[-1]).stem
(D/'outputs'/(name+'.receipt.json')).write_text(json.dumps({'cmd':cmd,'exit_code':rc,'wall_seconds':time.monotonic()-start,'peak_sampled_private_RSS_bytes':peak,'cpus':cpus,'cpu_seconds_cap':120,'wall_seconds_cap':140,'private_RSS_cap_bytes':6*1024**3,'address_space_cap_bytes':64*1024**3,'reason':reason,'trust_limit':'prebuilt read-only pinned upstream oleans trusted; 25ms RSS samples may miss transients'},indent=2));sys.exit(rc)
