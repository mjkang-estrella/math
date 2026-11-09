import pathlib,subprocess,os,resource,time,json
L=pathlib.Path(__file__).resolve().parent;F=L.parents[3]/'2026-10-14/formal'
F=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal');binary='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(p/'/.lake/build/lib/lean') for p in []]+[str(p/'.lake/build/lib/lean')for p in (F/'.lake/packages').iterdir()]+[str(F/'.lake/build/lib/lean')])
def limits():
 os.sched_setaffinity(0,{0,1});resource.setrlimit(resource.RLIMIT_AS,(8*1024**3,8*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(100,100))
t=time.time()
with open(L/('Latin-'+str(time.time_ns())+'.log'),'w') as log:
 try:r=subprocess.run([binary,'-j1','-DwarningAsError=true',str(L/'Latin.lean')],env=env,stdout=log,stderr=subprocess.STDOUT,timeout=110,preexec_fn=limits);rc=r.returncode
 except subprocess.TimeoutExpired:rc='wall timeout'
(L/'lean-run.json').write_text(json.dumps({'returncode':rc,'elapsed':time.time()-t,'LEAN_PATH':env['LEAN_PATH'],'binary':binary,'CPU_limit_s':100,'AS_limit_bytes':8*1024**3,'wall_limit_s':110},indent=2));print('Exit',rc)
