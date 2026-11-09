import os,pathlib,subprocess,time,json,resource,shutil,signal
resource.setrlimit(resource.RLIMIT_CPU,(120,120));os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
lane=pathlib.Path(__file__).resolve().parent;src=lane.parent/'nut-formal-r7q/formal';out=lane/'spotcheck';out.mkdir(exist_ok=True)
lean=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
pkgs=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
env=dict(os.environ,MALLOC_ARENA_MAX='2',HOME=str(out),TMPDIR=str(out),LEAN_PATH=':'.join([str(out),str(src)]+[str(p) for p in pkgs.glob('*/.lake/build/lib/lean')]))
results=[]
for name in ['FullCofactor','SignedEnumeration','Nut8Final']:
 shutil.copyfile(src/(name+'.lean'),out/(name+'.lean'))
 cmd=[str(lean),'-j2','-DwarningAsError=true','-o',name+'.olean',name+'.lean'];start=time.monotonic();peak=0
 def limit():resource.setrlimit(resource.RLIMIT_CPU,(120,120))
 with (out/(name+'.log')).open('wb') as log:
  p=subprocess.Popen(cmd,cwd=out,env=env,stdout=log,stderr=subprocess.STDOUT,preexec_fn=limit,start_new_session=True)
  killed=None
  while p.poll() is None:
   try:
    status=pathlib.Path('/proc')/str(p.pid)/'status';rss=int(next(x.split()[1] for x in status.read_text().splitlines() if x.startswith('VmRSS:')))*1024;peak=max(peak,rss)
    if rss>6*1024**3:killed='RSS cap'
   except (FileNotFoundError,StopIteration):pass
   if time.monotonic()-start>140:killed='wall cap'
   if killed:os.killpg(p.pid,signal.SIGKILL);break
   time.sleep(.1)
  rc=p.wait()
 r={'module':name,'command':cmd,'returncode':rc,'wall_seconds':time.monotonic()-start,'sampled_peak_rss_bytes':peak,'killed':killed,'imports':'inherited development oleans; independent spot check, NOT fresh closure replay'};results.append(r)
 print(json.dumps(r),flush=True)
(lane/'spotcheck.json').write_text(json.dumps(results,indent=2)+'\n')
