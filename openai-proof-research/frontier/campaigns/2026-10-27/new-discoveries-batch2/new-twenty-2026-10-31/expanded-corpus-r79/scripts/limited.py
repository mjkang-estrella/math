import os,resource,subprocess,sys,json,time,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
def cap():
 os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
name=sys.argv[1];start=time.time()
with (D/'outputs'/(name+'.log')).open('w') as f:
 try:r=subprocess.run(sys.argv[2:],stdout=f,stderr=subprocess.STDOUT,timeout=140,preexec_fn=cap);code=r.returncode
 except subprocess.TimeoutExpired:code='wall_timeout'
(D/'outputs'/(name+'-run.json')).write_text(json.dumps({'argv':sys.argv[2:],'elapsed_wall':time.time()-start,'exit':code,'cpu_seconds_cap':120,'wall_seconds_cap':140,'affinity_cpus':2,'address_space_bytes':6*1024**3},indent=2)+'\n')
print(name,code)
