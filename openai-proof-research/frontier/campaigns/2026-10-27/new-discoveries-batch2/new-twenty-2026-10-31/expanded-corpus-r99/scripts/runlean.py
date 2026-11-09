import pathlib,os,resource,subprocess,json,time
L=pathlib.Path.cwd();F=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal');P=F/'.lake/packages'
os.environ['LEAN_PATH']=':'.join(str(p)for p in P.glob('*/.lake/build/lib/lean'))
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(115,115));resource.setrlimit(resource.RLIMIT_AS,(64*1024**3,64*1024**3))
cmd=['/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean','-DwarningAsError=true','-o',str(L/'lean/PageRank.olean'),str(L/'lean/PageRank.lean')]
t=time.time()
with open('outputs/lean.log','w')as f:
 p=subprocess.Popen(cmd,stdout=f,stderr=subprocess.STDOUT);peak=0
 while p.poll() is None:
  try:
   vals={r.split(':')[0]:r.split(':')[1].strip()for r in pathlib.Path(f'/proc/{p.pid}/status').read_text().splitlines()if ':'in r};rss=int(vals.get('VmRSS','0 kB').split()[0]);peak=max(peak,rss)
   if rss>6*1024**2 or time.time()-t>130:p.kill()
  except FileNotFoundError:pass
  time.sleep(.2)
 p.wait()
json.dump({'cmd':cmd,'exit':p.returncode,'wall':time.time()-t,'peak_RSS_KiB':peak,'LEAN_PATH':os.environ['LEAN_PATH']},open('outputs/lean-run.json','w'),indent=2)
print(pathlib.Path('outputs/lean.log').read_text());print('exit',p.returncode)
