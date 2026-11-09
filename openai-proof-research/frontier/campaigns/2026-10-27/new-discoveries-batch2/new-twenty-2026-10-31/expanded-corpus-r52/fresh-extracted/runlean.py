import os,pathlib,subprocess,resource,sys,time,json
r=pathlib.Path(__file__).resolve().parent
base=r.parents[3]/'2026-10-14/formal/.lake/packages'
# absolute pinned cache, read only
base=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
env={'PATH':'/usr/bin:/bin','LC_ALL':'C.UTF-8'};env['LEAN_PATH']=':'.join(str(p/'.lake/build/lib/lean') for p in base.iterdir())+':'+str(r)
def limits():
 os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_AS,(12*1024**3,12*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(110,110))
cmd=['/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean','-j2','-DwarningAsError=true',*sys.argv[1:]]
p=subprocess.run(cmd,cwd=r,env=env,preexec_fn=limits,capture_output=True,text=True,timeout=120)
log=r/('lean-'+str(time.time_ns())+'.log');log.write_text(p.stdout+p.stderr);print(p.stdout+p.stderr);print('exit',p.returncode,'log',log.name)

sys.exit(p.returncode)
