import pathlib,json,subprocess,resource,os,sys,time
p=pathlib.Path(__file__).resolve().parent;d=json.loads((p/'lean-env.json').read_text());env=os.environ.copy();env['LEAN_PATH']=d['LEAN_PATH']
def limits():
 resource.setrlimit(resource.RLIMIT_AS,(8*1024**3,8*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(150,150));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
f=sys.argv[1] if len(sys.argv)>1 else 'MatchingCertificate.lean';t=time.monotonic()
with (p/(f+'.log')).open('w') as out:
 try:r=subprocess.run(['timeout','170',d['lean'],'-j1','-M6000',str(p/f)],env=env,stdout=out,stderr=subprocess.STDOUT,preexec_fn=limits,timeout=175);code=r.returncode
 except subprocess.TimeoutExpired:code='timeout'
(p/(f+'.run.json')).write_text(json.dumps({'exit':code,'elapsed':time.monotonic()-t,'limits':{'cpus':2,'cpu_seconds':150,'wall_seconds':170,'address_space_GiB':8,'lean_memory_MB':6000}},indent=2));print(code,flush=True)
